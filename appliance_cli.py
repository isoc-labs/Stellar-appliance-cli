#!/usr/bin/env python3
"""
Copyright (c) 2026, Stellar Cyber Inc.

Appliance Command Line Interface (CLI)

Date: 2026-01-01

"""

from __future__ import annotations
from dataclasses import dataclass
from typing import Sequence, Optional
from pathlib import Path

import datetime
import getpass
import json
import os
import os.path
import re
import sys
import cmd
import pwd
import functools
import grp
import stat

try:
    import readline
except Exception:
    readline = None

import socket
import signal
import subprocess
import shutil
import struct
import ctypes
import ctypes.util
import hmac
import logging
import logging.handlers
import ipaddress
import shlex
import termios
import tempfile


MGT_CONFIG_PATH = "/etc/network/interfaces.d/01-mgt.cfg"
NETWORK_INTERFACES_PATH = "/etc/network/interfaces"
NETWORK_INTERFACES_DIR = "/etc/network/interfaces.d"
NTPSEC_CONFIG_PATH = "/etc/ntpsec/ntp.conf"
NTPSEC_SERVICE = "ntpsec"
NTPSEC_QUERY_COMMAND = ["ntpq", "-pn"]


def _get_invoking_username():
    """Resolve the sudo caller from sudo-managed identity metadata."""
    if os.geteuid() != 0:
        return None

    sudo_uid = os.environ.get("SUDO_UID")
    sudo_user = os.environ.get("SUDO_USER")
    if sudo_uid is not None:
        try:
            username = pwd.getpwuid(int(sudo_uid)).pw_name
        except (KeyError, TypeError, ValueError, OverflowError):
            return None
        if sudo_user and sudo_user != username:
            return None
        return username

    # SUDO_USER without its paired SUDO_UID is inconsistent and is not trusted.
    if sudo_user:
        return None
    try:
        return pwd.getpwuid(os.getuid()).pw_name
    except KeyError:
        return None


def _verify_system_account_password(username, password, shadow_path="/etc/shadow"):
    """Verify a password against the invoking Unix account's shadow hash."""
    if not username or not password or "\x00" in username or "\x00" in password:
        return False

    try:
        pwd.getpwnam(username)
        stored_hash = None
        with open(shadow_path, "r", encoding="utf-8") as shadow_file:
            for entry in shadow_file:
                fields = entry.rstrip("\n").split(":")
                if len(fields) > 1 and fields[0] == username:
                    stored_hash = fields[1]
                    break
    except (OSError, KeyError, UnicodeError):
        return False

    # Locked or unset account passwords must not authorize a root shell.
    if not stored_hash or stored_hash.startswith(("!", "*")):
        return False

    library_name = ctypes.util.find_library("crypt")
    if not library_name:
        return False

    try:
        libcrypt = ctypes.CDLL(library_name)
        crypt_function = libcrypt.crypt
        crypt_function.argtypes = [ctypes.c_char_p, ctypes.c_char_p]
        crypt_function.restype = ctypes.c_char_p
        candidate = crypt_function(
            password.encode("utf-8"), stored_hash.encode("utf-8")
        )
        if not candidate:
            return False
        candidate_hash = candidate.decode("utf-8")
        return hmac.compare_digest(candidate_hash, stored_hash)
    except (AttributeError, OSError, UnicodeError, ValueError):
        return False


class _AtomicCommitError(Exception):
    def __init__(self, cause, replaced):
        super().__init__(str(cause))
        self.replaced = replaced


def _prepare_atomic_text_file(path, text):
    """Fully prepare a same-directory temporary replacement for *path*."""
    path = os.fspath(path)
    directory = os.path.dirname(path) or "."
    stat_result = os.stat(path) if os.path.exists(path) else None
    fd = None
    temporary_path = None
    try:
        fd, temporary_path = tempfile.mkstemp(
            prefix=".{}.".format(os.path.basename(path)),
            dir=directory,
            text=True,
        )
        if stat_result is not None:
            os.fchmod(fd, stat_result.st_mode & 0o7777)
            try:
                os.fchown(fd, stat_result.st_uid, stat_result.st_gid)
            except PermissionError:
                current = os.fstat(fd)
                if (current.st_uid, current.st_gid) != (stat_result.st_uid, stat_result.st_gid):
                    raise
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as stream:
            fd = None
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        prepared_path = temporary_path
        temporary_path = None
        return prepared_path
    finally:
        if fd is not None:
            os.close(fd)
        if temporary_path is not None:
            try:
                os.unlink(temporary_path)
            except FileNotFoundError:
                pass


def _commit_prepared_text_file(path, temporary_path):
    """Replace *path* with a prepared file and fsync its directory."""
    path = os.fspath(path)
    directory = os.path.dirname(path) or "."
    try:
        os.replace(temporary_path, path)
    except Exception as exc:
        raise _AtomicCommitError(exc, replaced=False) from exc
    try:
        directory_fd = os.open(directory, os.O_RDONLY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except Exception as exc:
        raise _AtomicCommitError(exc, replaced=True) from exc


def _atomic_replace_text_file(path, text):
    """Prepare and atomically commit one text file replacement."""
    temporary_path = None
    try:
        temporary_path = _prepare_atomic_text_file(path, text)
        _commit_prepared_text_file(path, temporary_path)
        temporary_path = None
    finally:
        if temporary_path is not None:
            try:
                os.unlink(temporary_path)
            except FileNotFoundError:
                pass



def _syslog_gid():
    try:
        return grp.getgrnam("syslog").gr_gid
    except KeyError:
        return 0


def _ensure_root_owned_directory(path, group_name="syslog", mode=0o750):
    """Create a directory without following symlinks, then enforce root ownership."""
    if os.geteuid() != 0:
        raise PermissionError("Root privileges are required to secure {}".format(path))
    target = Path(path)
    if not target.is_absolute():
        raise ValueError("Security-sensitive directory must be absolute: {}".format(path))

    current = Path("/")
    for component in target.parts[1:]:
        current = current / component
        if os.path.lexists(current):
            current_stat = os.lstat(current)
            if stat.S_ISLNK(current_stat.st_mode) or not stat.S_ISDIR(current_stat.st_mode):
                raise RuntimeError("Refusing unsafe directory component: {}".format(current))
        else:
            os.mkdir(current, 0o755 if current.parent == Path("/") else 0o750)

    try:
        gid = grp.getgrnam(group_name).gr_gid
    except KeyError:
        gid = 0
    os.chown(str(target), 0, gid)
    os.chmod(str(target), mode)
    return gid


def _secure_existing_log_files(directory, prefix, gid):
    """Remove planted links/special files and secure existing CLI log files."""
    for entry in os.scandir(directory):
        if not entry.name.startswith(prefix):
            continue
        entry_stat = entry.stat(follow_symlinks=False)
        if not stat.S_ISREG(entry_stat.st_mode) or entry_stat.st_nlink != 1:
            os.unlink(entry.path)
            continue
        os.chown(entry.path, 0, gid)
        os.chmod(entry.path, 0o640)


def _ensure_patch_storage():
    _ensure_root_owned_directory("/var/lib/aella", mode=0o750)
    _ensure_root_owned_directory(PATCH_DIR, mode=0o750)
    _ensure_root_owned_directory(PATCH_LOG_DIR, mode=0o750)


def _read_root_text_file(path):
    """Read a root-owned regular file without following a symlink."""
    flags = os.O_RDONLY | getattr(os, "O_NOFOLLOW", 0)
    fd = os.open(os.fspath(path), flags)
    try:
        file_stat = os.fstat(fd)
        if not stat.S_ISREG(file_stat.st_mode) or file_stat.st_nlink != 1 or file_stat.st_uid != 0:
            raise RuntimeError("Refusing unsafe state file: {}".format(path))
        with os.fdopen(fd, "r", encoding="utf-8") as stream:
            fd = -1
            return stream.read()
    finally:
        if fd >= 0:
            os.close(fd)


def _write_root_text_file(path, content, mode=0o640):
    path = Path(path)
    _ensure_root_owned_directory(str(path.parent), mode=0o750)
    _atomic_replace_text_file(str(path), content)
    os.chown(str(path), 0, _syslog_gid())
    os.chmod(str(path), mode)


# Timezone constants
try:
    from zoneinfo import available_timezones
    ALL_TIMEZONES = frozenset(available_timezones())
except Exception:
    ALL_TIMEZONES = frozenset()

# Logging utilities
LOG_DIR = "/var/log/aella" if os.geteuid() == 0 else tempfile.mkdtemp(prefix="aella_cli_test_")
ACL_STAGING_PATH = "/var/lib/aella/acl_staging.json"
ACL_STATE_PATH = "/var/lib/aella/acl_state.json"
ACL_COMMENT_PREFIX = "AELLA_ACL "
ACL_AUTO_COMMENT = "AELLA_ACL_AUTO Current SSH session"
LOCAL_ALWAYS_ALLOW_COMMENT = "AELLA_LOCAL_ALWAYS_ALLOW"
ALWAYS_ALLOW_DEST_IPS = ["127.0.0.1", "192.168.0.100", "192.168.122.1"]
AELLA_INPUT_CHAIN = "AELLA_INPUT"
AELLA_SYSTEM_ALLOW_ESTABLISHED_COMMENT = "AELLA_SYSTEM Allow established"
AELLA_SYSTEM_JUMP_COMMENT = "AELLA_SYSTEM Jump to AELLA_INPUT"
AELLA_DEFAULT_WHITELIST_COMMENT = "AELLA_DEFAULT Whitelist deny all"
AELLA_DEFAULT_BLACKLIST_COMMENT = "AELLA_DEFAULT Blacklist allow all"
ACL_EXCLUDE_IPS = ("192.168.0.100", "192.168.122.1")
ACL_EXCLUDE_IP = ACL_EXCLUDE_IPS[0]


def get_username():
    return pwd.getpwuid(os.getuid())[0]


def print_log(msg: str, logger: logging.Logger | None = None, level: int = logging.INFO) -> None:
    print(msg)
    if logger:
        logger.log(level, msg)


def make_dir(target_dir, group=None, logger=None, root=False):
    target_path = Path(target_dir)
    try:
        if root:
            proc = subprocess.run(
                ["sudo", "mkdir", "-p", str(target_path)],
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
        else:
            target_path.mkdir(parents=True, exist_ok=True)
            proc = subprocess.CompletedProcess([], 0, "", "")
    except PermissionError:
        proc = subprocess.run(
            ["sudo", "mkdir", "-p", str(target_path)],
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
    except Exception as e:
        err_msg = str(e)
        print_log("Failed to create directory {}: {}".format(target_dir, err_msg), logger, level=logging.ERROR)
        return False
    
    if proc.returncode != 0:
        err_msg = proc.stderr
        if "Permission denied" in err_msg:
            user = get_username()
            if group is None:
                group = user  # use same group as user
            proc2 = subprocess.run(
                ["sudo", "usermod", "-a", "-G", group, user],
                check=False,
            )
            if proc2.returncode != 0:
                print_log("Failed to add {} into {} group".format(user, group), logger, level=logging.ERROR)
                return False
        else:
            print_log("Failed to create directory {}: {}".format(target_dir, err_msg), logger, level=logging.ERROR)
            return False
    return True


def ensure_file(file_path, root=False, owner=None):
    if owner is None:
        owner = get_username()
    base_dir = os.path.dirname(file_path)
    if not make_dir(base_dir, root=root):
        print_log("Failed to create directory {}".format(base_dir), level=logging.ERROR)
        return False
    file_path_obj = Path(file_path)
    try:
        if root:
            proc = subprocess.run(
                ["sudo", "touch", str(file_path_obj)],
                check=False,
            )
        else:
            file_path_obj.touch(exist_ok=True)
            proc = subprocess.CompletedProcess([], 0, "", "")
    except PermissionError:
        proc = subprocess.run(
            ["sudo", "touch", str(file_path_obj)],
            check=False,
        )
    except Exception:
        proc = subprocess.run(
            ["sudo", "touch", str(file_path_obj)],
            check=False,
        )
    
    if proc.returncode != 0:
        print_log("Failed to create file {}".format(file_path), level=logging.ERROR)
        return False
    if owner != "root":
        chown_cmd = ["chown", owner, str(file_path_obj)]
        if root:
            chown_cmd = ["sudo"] + chown_cmd
        proc = subprocess.run(chown_cmd, check=False)
        if proc.returncode != 0:
            print_log("Failed to change owner of file {}".format(file_path), level=logging.ERROR)
            return False
    return True


class RotatingFileHandler(logging.handlers.RotatingFileHandler):
    def __init__(self, filename, *args, **kwargs):
        directory = os.path.dirname(filename)
        if os.geteuid() == 0:
            gid = _ensure_root_owned_directory(directory, mode=0o750)
            _secure_existing_log_files(directory, os.path.basename(filename), gid)
        else:
            directory_path = Path(directory)
            if os.path.lexists(directory_path):
                directory_stat = os.lstat(directory_path)
                if stat.S_ISLNK(directory_stat.st_mode) or not stat.S_ISDIR(directory_stat.st_mode):
                    raise RuntimeError("Refusing unsafe log directory: {}".format(directory))
            else:
                directory_path.mkdir(parents=True, mode=0o700)
            os.chmod(directory, 0o700)
        super(RotatingFileHandler, self).__init__(filename, *args, **kwargs)
        if os.geteuid() == 0:
            os.chown(filename, 0, _syslog_gid())
            os.chmod(filename, 0o640)


def get_logger(log_name):
    filename = os.path.join(LOG_DIR, "{}.log".format(log_name))
    logger = logging.getLogger(log_name)
    if logger.handlers:
        return logger
    logger.setLevel(logging.INFO)
    formatter = logging.Formatter(
        "%(asctime)-15s|%(levelname)s|%(thread)d|%(module)s|%(message)s"
    )
    handler = RotatingFileHandler(
        filename,
        maxBytes=10 * 1024 * 1024,
        backupCount=5,
    )
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    return logger


LOG = get_logger("aella_cli")


def log_cmd(f):
    @functools.wraps(f)
    def wrapper(*args, **kwds):
        LOG.info('Run command: %s %s', f.__name__[3:], " ".join(args[1:]))
        return f(*args, **kwds)
    return wrapper

META_USER = "AellaMeta"

META_TOKEN = "WroTQfm/W6x10"

PATCH_DIR = "/var/lib/aella/hotfix"
PATCH_LOG_DIR = "{}/logs".format(PATCH_DIR)
PATCH_HISTORY = "{}/hotfix-history".format(PATCH_DIR)


@dataclass(frozen=True)
class CmdResult:
    args: Sequence[str]
    returncode: int
    stdout: str
    stderr: str


def run_cmd(args: Sequence[str], *, check: bool = True, timeout: Optional[int] = None) -> CmdResult:
    proc = subprocess.run(
        list(args),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
        timeout=timeout,
    )
    if check and proc.returncode != 0:
        raise subprocess.CalledProcessError(
            proc.returncode, list(args),
            output=proc.stdout, stderr=proc.stderr
        )
    return CmdResult(
        args=list(args),
        returncode=proc.returncode,
        stdout=proc.stdout,
        stderr=proc.stderr,
    )


class AellaCli(cmd.Cmd, object):
    """Aella Data Appliance CLI"""
    intro = '\nWelcome to Starlight Appliance\n'
    prompt = 'Appliance> '

    def __init__(self):
        cmd.Cmd.__init__(self)

        # Enable TAB completion (readline)
        if readline:
            try:
                readline.parse_and_bind('tab: complete')
            except Exception:
                pass
            # Treat '-' as part of a word so 'dl-master' can be completed
            try:
                readline.set_completer_delims(' \t\n')
            except Exception:
                pass

        # Root command help
        self.root_command_help = {
            'console': 'Jump to dl-master, da-master(aka dr-master), mds, or aio console',
            'show': 'Display Component Information',
            'set': 'Configure Component Parameters',
            'unset': 'Unset Configuration',
            'shutdown': 'Shutdown System or Service',
            'start': 'Start System or Service',
            'restart': 'Restart System or Service',
            'clear': 'Clear History',
            'monitor': 'Monitor VM resources and system health',
            'quit': 'Exit CLI',
            'help': 'Display Help Information',
        }

        # Show command help
        self.show_command_help = {
            'version': 'Show System Information',
            'hostname': 'Show Hostname',
            'service': 'Show Service Information',
            'interface': 'Show Interface Information',
            'timezone': 'Show Timezone Information',
            'time': 'Show System Time',
            'ntp': 'Show NTP Information',
            'gateway': 'Show Default Gateway Information',
            'dns': 'Show DNS Server Information',
            'route': 'Show Routing Table', 
            'cli': 'Show CLI History',
            'patch_history': 'Show the History of Patches Applied',
            'autostart': 'Show VM Auto Start Configuration',
            'acl': 'Show Access Control List (iptables rules)',
        }

        # Show command callback
        self.show_command_callback = {
            'version': self.show_version,
            'hostname': self.show_hostname,
            'service': self.show_service,
            'interface': self.show_interface_callback,
            'timezone': self.show_tz_callback,
            'time': self.show_time_callback,
            'ntp': self.show_ntp_callback,
            'gateway': self.show_gateway_callback,
            'dns': self.show_dns_callback,
            'route': self.show_route_callback,
            'cli': self.show_cli_callback,
            'patch_history': self.show_patch_history_callback,
            'autostart': self.show_autostart_callback,
            'acl': self.show_acl_callback,
        }

        # Set command help
        self.set_command_help = {
            'password': 'Configure Admin Password',
            'timezone': 'Configure System Timezone',
            'time': 'Configure System Time',
            'ntp': 'Configure NTP Server',
            'interface': 'Configure Interface Parameters',
            'dns': 'Configure DNS Server for Interface',
            'hostname': 'Configure Host Name',
            'patches': 'Apply patches/update',
            'autostart': 'Configure VM Auto Start',
            'acl': 'Configure Access Control List (iptables rules)',
        }

        # Set command callback
        self.set_command_callback = {
            'password': self.set_password_callback,
            'timezone': self.set_tz_callback,
            'time': self.set_time_callback,
            'ntp': self.set_ntp_callback,
            'interface': self.set_interface_callback,
            'dns': self.set_dns_callback,
            'hostname': self.set_hostname_callback,
            'patches': self.set_patches_callback,
            'patch': self.set_patches_callback,
            'autostart': self.set_autostart_callback,
            'acl': self.set_acl_callback,
        }

        self.unset_command_help = {
            'ntp': 'Unset NTP Server',
            'interface': 'Unset interface configuration',
            'acl': 'Unset Access Control List (iptables rules)'
        }

        self.unset_command_callback = {
            'ntp': self.unset_ntp_callback,
            'interface': self.unset_interface_callback,
            'acl': self.unset_acl_callback
        }

        # Dynamically build start command help and callback from virsh list
        self.start_command_help = {}
        self.start_command_callback = {}
        vm_list = self.get_vm_list()
        for vm in vm_list:
            self.start_command_help[vm] = 'Start {}'.format(vm)
            self.start_command_callback[vm] = self._create_vm_start_callback(vm)

        # Dynamically build restart command help and callback from virsh list
        self.restart_command_help = {'system': 'Reboot appliance'}
        self.restart_command_callback = {'system': self.restart_system_callback}
        vm_list = self.get_vm_list()
        for vm in vm_list:
            self.restart_command_help[vm] = 'Restart {}'.format(vm)
            self.restart_command_callback[vm] = self._create_vm_restart_callback(vm)

        # Dynamically build shutdown command help and callback from virsh list
        self.shutdown_command_help = {'system': 'Shutdown appliance'}
        self.shutdown_command_callback = {'system': self.shutdown_system_callback}
        vm_list = self.get_vm_list()
        for vm in vm_list:
            self.shutdown_command_help[vm] = 'Shutdown {}'.format(vm)
            self.shutdown_command_callback[vm] = self._create_vm_shutdown_callback(vm)

        # Dynamically build console command help and callback from virsh list
        self.console_command_help = {}
        self.console_command_callback = {}
        vm_list = self.get_vm_list()
        for vm in vm_list:
            self.console_command_help[vm] = 'Go to {} console'.format(vm)
            self.console_command_callback[vm] = self._create_vm_console_callback(vm)

        self.clear_command_help = {
            'cli': 'Clear CLI history',
        }

        self.clear_command_callback = {
            'cli': self.clear_cli_callback,
        }

        # Monitor command
        self.monitor_command_help = {
            'vm': 'Monitor VM resource usage',
            'system': 'Check system health status',
        }

        self.monitor_command_callback = {
            'vm': self.monitor_vm_callback,
            'system': self.monitor_system_callback,
        }

        # Shell command
        self.shell_command = [
            'ping', 'tcpdump', 'traceroute', 'ifconfig', 'iptables', 'dmesg', 'ip', 'dig', 'htop', 'top'
        ]

    # Main loop
    def cmdloop(self, intro=None):
        print(self.intro)
        while True:
            try:
                super(AellaCli, self).cmdloop(intro="")
                self.postloop()
                break
            except KeyboardInterrupt:
                print("^C")

    @staticmethod
    def get_da_name():
        try:
            rc = run_cmd(["virsh", "dominfo", "da-master"], check=False).returncode
            return "da-master" if rc == 0 else "dr-master"
        except Exception:
            return 'dr-master'

    @staticmethod
    def get_vm_list():
        """Get list of all VMs from virsh list --all"""
        vm_list = []
        try:
            result = run_cmd(["virsh", "list", "--all", "--name"], check=False)
            if result.stdout:
                vm_list = [vm.strip() for vm in result.stdout.split('\n') if vm.strip()]
        except Exception:
            pass
        return vm_list

    def completenames(self, text, line, begidx, endidx):
        if not text:
            completions = self.root_command_help.keys()
        else:
            completions = [f for f in self.root_command_help.keys() if f.startswith(text)]
        return completions

    def complete_console(self, text, line, begidx, endidx):
        # console <vmname> completion
        keys = list(self.console_command_help.keys())
        if not text:
            return keys
        return [k for k in keys if k.startswith(text)]

    def is_password_valid(self):
        passcode = getpass.getpass('Password: ')
        if not passcode:
            return False

        username = _get_invoking_username()
        if not username:
            return False
        # A user already running the CLI as root does not need an additional gate.
        if username == "root":
            return True
        return _verify_system_account_password(username, passcode)

    @staticmethod
    def _on_nested_command(line, help_meta, callback_meta):
        key = ''
        param = ''
        if line:
            key = line.split()[0]
            param = line.split()[1:]
        if key and key in callback_meta:
            callback = callback_meta.get(key)
            if callback:
                callback(key, param)
        elif not key or key == '?' or key == 'help':
            print('')
            for cmd in sorted(help_meta.keys()):
                print('{:15} {}'.format(cmd, help_meta[cmd]))
            print('')
        else:
            partial_matched = False
            for full_key in help_meta.keys():
                if full_key.startswith(key):
                    partial_matched = True
                    key = full_key
                    break
            if partial_matched:
                callback = callback_meta.get(key)
                if callback:
                    callback(key, param)
            else:
                print("*** Unknown syntax: {}".format(line))

    # Help command
    def do_help(self, line):
        """Display help information for commands"""
        if not line or line.strip() == '':
            # Show main help menu
            print('')
            print('Available Commands:')
            print('=' * 70)
            for cmd in sorted(self.root_command_help.keys()):
                if cmd != 'help':  # Don't show help command in the list
                    print('{0:15} {1}'.format(cmd, self.root_command_help[cmd]))
            print('')
            print('To get help for a specific command: help <command>')
            print('To get help for nested commands (show, set): <command> help')
            print('To run system commands directly: !<command> (e.g., !ping)')
            print('')
        else:
            # Show help for specific command
            cmd_name = line.strip().split()[0]
            if cmd_name in self.root_command_help:
                print('')
                print('Command: {}'.format(cmd_name))
                print('Description: {}'.format(self.root_command_help[cmd_name]))
                print('')
                # Show nested command help if available
                if cmd_name == 'show' and hasattr(self, 'show_command_help'):
                    print('Available sub-commands:')
                    for sub_cmd in sorted(self.show_command_help.keys()):
                        print('  {0:15} {1}'.format(sub_cmd, self.show_command_help[sub_cmd]))
                    print('')
                    print('Usage: show <sub-command>')
                elif cmd_name == 'set' and hasattr(self, 'set_command_help'):
                    print('Available sub-commands:')
                    for sub_cmd in sorted(self.set_command_help.keys()):
                        print('  {0:15} {1}'.format(sub_cmd, self.set_command_help[sub_cmd]))
                    print('')
                    print('Usage: set <sub-command> [parameters]')
                elif cmd_name == 'unset' and hasattr(self, 'unset_command_help'):
                    print('Available sub-commands:')
                    for sub_cmd in sorted(self.unset_command_help.keys()):
                        print('  {0:15} {1}'.format(sub_cmd, self.unset_command_help[sub_cmd]))
                    print('')
                    print('Usage: unset <sub-command>')
                elif cmd_name in ['start', 'restart', 'shutdown']:
                    if hasattr(self, '{}_command_help'.format(cmd_name)):
                        help_dict = getattr(self, '{}_command_help'.format(cmd_name))
                        if help_dict:
                            print('Available options:')
                            for sub_cmd in sorted(help_dict.keys()):
                                print('  {0:15} {1}'.format(sub_cmd, help_dict[sub_cmd]))
                            print('')
                            print('Usage: {} <option>'.format(cmd_name))
                elif cmd_name == 'console':
                    if hasattr(self, 'console_command_help'):
                        if self.console_command_help:
                            print('Available console options:')
                            for sub_cmd in sorted(self.console_command_help.keys()):
                                print('  {0:15} {1}'.format(sub_cmd, self.console_command_help[sub_cmd]))
                            print('')
                            print('Usage: console <vm-name>')
                        else:
                            print('No VMs available for console access.')
                            print('')
                elif cmd_name == 'monitor':
                    print('Usage: monitor')
                    print('Displays VM resources and system health information.')
                    print('')
            else:
                print('')
                print("Unknown command: '{}'".format(cmd_name))
                print('Type "help" to see available commands.')
                print('')

    def parseline(self, line):
        stripped = line.lstrip()
        if stripped.startswith("!"):
            return "bang", stripped[1:].strip(), line
        return super(AellaCli, self).parseline(line)

    def _resolve_shell_command(self, command):
        if command not in self.shell_command:
            return None
        executable = shutil.which(command, path="/usr/sbin:/usr/bin:/sbin:/bin")
        if not executable:
            return None
        resolved = os.path.realpath(executable)
        if not any(resolved.startswith(prefix) for prefix in ("/usr/bin/", "/usr/sbin/", "/bin/", "/sbin/")):
            return None
        try:
            executable_stat = os.stat(resolved)
        except OSError:
            return None
        if (
            not stat.S_ISREG(executable_stat.st_mode)
            or executable_stat.st_uid != 0
            or executable_stat.st_mode & 0o022
        ):
            return None
        return resolved

    def _is_safe_shell_diagnostic(self, tokens):
        """Fail-closed argument policy for the explicitly allowed diagnostic tools."""
        if not tokens or tokens[0] not in self.shell_command:
            return False
        command, args = tokens[0], tokens[1:]

        if command == "ip":
            allowed_flags = {
                "-4", "-6", "-br", "-brief", "-s", "-stats", "-d",
                "-details", "-o", "-oneline", "-r", "-resolve", "-numeric",
                "-j", "-json",
            }
            index = 0
            while index < len(args) and args[index].startswith("-"):
                flag = args[index]
                if flag in allowed_flags:
                    index += 1
                elif flag == "-family" and index + 1 < len(args) and args[index + 1] in {"inet", "inet6", "link"}:
                    index += 2
                else:
                    return False
            if index >= len(args):
                return True
            object_name = args[index]
            remaining = args[index + 1:]
            if object_name == "netns":
                return remaining == ["list"]
            if object_name not in {"addr", "address", "link", "route", "neigh", "neighbor", "rule"}:
                return False
            if not remaining:
                return True
            return remaining[0] in {"show", "list"} or (
                object_name == "route" and remaining[0] == "get"
            )

        if command == "tcpdump":
            return not any(
                token in {"-z", "-w", "--postrotate-command", "--write"}
                or token.startswith(("-z", "-w"))
                for token in args
            )

        if command == "dmesg":
            return not any(
                token in {
                    "-c", "--read-clear", "-C", "--clear", "-n",
                    "--console-level", "-D", "-E",
                }
                or token.startswith("--console-level=")
                for token in args
            )

        if command == "iptables":
            tables = {"filter", "nat", "mangle", "raw", "security"}
            read_only_flags = {
                "-n", "--numeric", "-v", "--verbose", "-x", "--exact",
                "--line-numbers", "-w",
            }
            index = 0
            while index < len(args):
                token = args[index]
                if token == "-t" and index + 1 < len(args) and args[index + 1] in tables:
                    index += 2
                elif token in read_only_flags:
                    index += 1
                else:
                    break
            if index >= len(args) or args[index] not in {"-L", "--list", "-S", "--list-rules"}:
                return False
            for token in args[index + 1:]:
                if token in read_only_flags:
                    continue
                if token.startswith("-") or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,64}", token):
                    return False
            return True

        if command == "ifconfig":
            return len(args) <= 1 and (
                not args or args == ["-a"]
                or re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", args[0]) is not None
            )

        if command == "top":
            if "-n" in args:
                index = args.index("-n")
                if index + 1 >= len(args) or not args[index + 1].isdigit():
                    return False
                if not 1 <= int(args[index + 1]) <= 10:
                    return False
            return True

        if command == "ping":
            for index, token in enumerate(args):
                if token in {"-f", "--flood", "-l", "--preload"} or token.startswith("--flood="):
                    return False
                if token in {"-c", "--count"}:
                    if index + 1 >= len(args) or not args[index + 1].isdigit():
                        return False
                    if not 1 <= int(args[index + 1]) <= 20:
                        return False
                if token.startswith("-c") and token[2:].isdigit():
                    if not 1 <= int(token[2:]) <= 20:
                        return False
            return True

        if command in {"traceroute", "dig", "htop"}:
            return True

        return False

    @log_cmd
    def do_shell(self, line):
        """Enter the maintenance shell only after authenticating the invoking account."""
        if line.strip():
            print("The 'shell' command does not accept arguments. Use !<allowed-command> for diagnostics.")
            return
        if not self.is_password_valid():
            print("Authentication failed. Use 'set password' to set your account password.")
            return
        try:
            subprocess.call(["/bin/bash", "--login"], cwd="/root", shell=False)
        except Exception as exc:
            print("Failed to start maintenance shell: {}".format(exc))

    @log_cmd
    def do_bang(self, line):
        """Run one explicitly allowlisted diagnostic command without a shell."""
        try:
            tokens = shlex.split(line)
        except ValueError as exc:
            print("Invalid diagnostic command: {}".format(exc))
            return
        if not tokens or tokens[0] not in self.shell_command:
            print("Command is not in the diagnostic allowlist.")
            return
        if not self._is_safe_shell_diagnostic(tokens):
            print("Command or arguments are restricted on the diagnostic path.")
            return

        executable = self._resolve_shell_command(tokens[0])
        if not executable:
            print("Allowed diagnostic command is not installed or is not a trusted system binary.")
            return

        command = tokens[0]
        args = tokens[1:]
        if command == "top":
            if not args:
                args = ["-b", "-n", "1"]
            elif "-b" not in args:
                args = ["-b", "-n", "1"] + args
            elif "-n" not in args:
                args.extend(["-n", "1"])

        user_scoped = {"ping", "traceroute", "dig", "htop", "top"}
        if command in user_scoped:
            username = _get_invoking_username()
            if not username:
                print("Unable to resolve the authenticated invoking account; command denied.")
                return
            if username != "root":
                argv = ["/usr/bin/sudo", "-u", username, "--", executable] + args
            else:
                argv = [executable] + args
        else:
            argv = [executable] + args

        env = {
            "PATH": "/usr/sbin:/usr/bin:/sbin:/bin",
            "TERM": os.environ.get("TERM", "xterm"),
            "LANG": os.environ.get("LANG", "C.UTF-8"),
        }
        try:
            subprocess.call(argv, shell=False, env=env)
        except Exception as exc:
            print("Command failed: {}".format(exc))

    @staticmethod
    def show_cmd_default_callback    @staticmethod
    def show_cmd_default_callback(key, param):
        if key:
            return None 

    # Restart command
    def complete_restart(self, text, line, begidx, endidx):
        if not text:
            completions = self.restart_command_help.keys()
        else:
            completions = [f for f in self.restart_command_help.keys() if f.startswith(text)]
        return completions

    @log_cmd
    def do_restart(self, line):
        """ Restart command """
        return self._on_nested_command(line, self.restart_command_help, self.restart_command_callback)

    def restart_system_callback(self, key, param):
        """Restart System."""
        ans = ""
        while ans not in {"Y", "n", "y", "N"}:
            ans = input("Restart Appliance, are you sure? [Y/n]: ")
        if ans in {"Y", "y"}:
            print("Restarting...")
            subprocess.run(["sync"], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL, check=False)
            subprocess.run(["reboot"], check=False)
        else:
            print("Restarting operation aborted.")

    def _create_vm_start_callback(self, vm_name):
        """Create a callback function for starting a VM."""
        def callback(key, param):
            if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm_name):
                print("Invalid VM name.")
                return
            subprocess.run(["virsh", "start", vm_name], check=False)
        return callback

    def _create_vm_restart_callback(self, vm_name):
        """Create a callback function for restarting a VM."""
        def callback(key, param):
            if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm_name):
                print("Invalid VM name.")
                return
            subprocess.run(["virsh", "reboot", vm_name], check=False)
        return callback

    def _create_vm_shutdown_callback(self, vm_name):
        """Create a callback function for shutting down a VM."""
        def callback(key, param):
            if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm_name):
                print("Invalid VM name.")
                return
            subprocess.run(["virsh", "shutdown", vm_name], check=False)
        return callback

    def _reset_console_terminal(self, saved_attrs=None):
        fd = sys.stdin.fileno()
        if saved_attrs is not None:
            try:
                termios.tcsetattr(fd, termios.TCSADRAIN, saved_attrs)
            except (termios.error, OSError, ValueError):
                pass
        try:
            with open("/dev/tty", "r") as tty:
                subprocess.call(["stty", "sane"], stdin=tty, stderr=subprocess.DEVNULL, stdout=subprocess.DEVNULL)
        except OSError:
            pass

    def _attach_vm_console(self, vm_name):
        """Attach to a VM serial/virtio console with proper TTY handoff."""
        if not sys.stdin.isatty() or not sys.stdout.isatty():
            print("\nConsole requires an interactive terminal.\n")
            return

        state = run_cmd(["virsh", "domstate", vm_name], check=False).stdout.strip()
        if state != "running":
            print("\nVM {} is not running (state: {}).\n".format(vm_name, state or "unknown"))
            return

        fd = sys.stdin.fileno()
        saved_attrs = None
        try:
            saved_attrs = termios.tcgetattr(fd)
        except (termios.error, OSError, ValueError):
            pass

        self._reset_console_terminal(saved_attrs)
        print("\nConnecting to {} console (Escape character is ^] )...\n".format(vm_name))
        rc = subprocess.call(["virsh", "console", "--force", vm_name])
        self._reset_console_terminal(saved_attrs)

        if rc != 0:
            print(
                "\nConsole disconnected from {}.\n"
                "This is normal if the guest rebooted or closed the console during bootstrap.\n"
                "Reconnect with: console {}\n".format(vm_name, vm_name)
            )
        else:
            print("")

    def _create_vm_console_callback(self, vm_name):
        """Create a callback function for console access to a VM"""
        def callback(key, param):
            self._attach_vm_console(vm_name)
        return callback

    def complete_start(self, text, line, begidx, endidx):
        if not text:
            completions = self.start_command_help.keys()
        else:
            completions = [f for f in self.start_command_help.keys() if f.startswith(text)]
        return completions

    @log_cmd
    def do_start(self, line):
        """ Start command """
        return self._on_nested_command(line, self.start_command_help, self.start_command_callback)


    def shutdown_system_callback(self, key, param):
        ans = ""
        while ans != "Y" and ans != "n" and ans != "y" and ans != "N":
            ans = input('Shutdown Appliance, are you sure? [Y/n]: ')
        if ans == "Y" or ans == "y":
            print('Shutting down...')
            self.shell_cmd_exec('shutdown -h now')
        else:
            print('Shutdown operation aborted.')


    # Quit command
    @log_cmd
    def do_quit(self, line):
        """ Quit"""
        return True

    def emptyline(self):
        return

    # Show command
    @log_cmd
    def do_show(self, line):
        """ Show command """
        return self._on_nested_command(line, self.show_command_help, self.show_command_callback)

    # Clear command
    @log_cmd
    def do_clear(self, line):
        """ Show command """
        return self._on_nested_command(line, self.clear_command_help, self.clear_command_callback)

    # Monitor command
    @log_cmd
    def do_monitor(self, line):
        """ Monitor command """
        return self._on_nested_command(line, self.monitor_command_help, self.monitor_command_callback)

    # Console command
    @log_cmd
    def do_console(self, line):
        """ Console command """
        return self._on_nested_command(line, self.console_command_help, self.console_command_callback)

    # Shutdown command
    def complete_shutdown(self, text, line, begidx, endidx):
        if not text:
            completions = self.shutdown_command_help.keys()
        else:
            completions = [f for f in self.shutdown_command_help.keys() if f.startswith(text)]
        return completions

    @log_cmd
    def do_shutdown(self, line):
        """Shutdown command """
        return self._on_nested_command(line, self.shutdown_command_help, self.shutdown_command_callback)

    def complete_show(self, text, line, begidx, endidx):
        if not text:
            completions = self.show_command_help.keys()
        elif line.startswith('show interface'):
            return self.complete_show_interface(text, line, begidx, endidx)
        else:
            completions = [f for f in self.show_command_help.keys() if f.startswith(text)]
        return completions

    # Need to use timedatectl to get the timezone for both Ubuntu 16.04 and 24.04
    def show_tz_callback(self, key, param):
        try:
            result = subprocess.check_output(
                ["timedatectl", "show", "-p", "Timezone", "--value"],
                stderr=subprocess.PIPE
            ).decode("utf-8").strip()
            if result:
                print("Timezone: {}".format(result))
            else:
                print("Timezone: (unknown)")
        except subprocess.CalledProcessError:
            print("Failed to retrieve timezone using timedatectl")

    def show_time_callback(self, key, param):
        self.shell_cmd_exec('date \"+%a %Y-%m-%d %H:%M:%S %Z\"')

    def _list_timezones(self) -> list[str]:
        try:
            out = subprocess.check_output(
                ["timedatectl", "list-timezones"],
                stderr=subprocess.PIPE
            ).decode().splitlines()
            timezones = [x.strip() for x in out if x.strip()]
            if timezones:
                return sorted(timezones)
        except Exception:
            pass
        if ALL_TIMEZONES:
            return sorted(ALL_TIMEZONES)
        return []

    _NTPSEC_BLOCK_BEGIN_TAGS = frozenset({
        "# === XDR_NTPSEC_CONFIG_BEGIN ===",
        "# XDR_NTPSEC_CONFIG_BEGIN",
    })
    _NTPSEC_BLOCK_END_TAGS = frozenset({
        "# === XDR_NTPSEC_CONFIG_END ===",
        "# XDR_NTPSEC_CONFIG_END",
    })
    _NTPSEC_MARKER_PAIRS = {
        "# === XDR_NTPSEC_CONFIG_BEGIN ===": "# === XDR_NTPSEC_CONFIG_END ===",
        "# XDR_NTPSEC_CONFIG_BEGIN": "# XDR_NTPSEC_CONFIG_END",
    }

    @staticmethod
    def _strip_ntp_conf_line(line):
        return line.replace('\r', '').strip()

    @classmethod
    def _is_ntpsec_block_begin(cls, line):
        return cls._strip_ntp_conf_line(line) in cls._NTPSEC_BLOCK_BEGIN_TAGS

    @classmethod
    def _is_ntpsec_block_end(cls, line):
        return cls._strip_ntp_conf_line(line) in cls._NTPSEC_BLOCK_END_TAGS

    def _parse_ntpsec_managed_block(self, lines, allow_absent=False):
        begins = [
            (index, self._strip_ntp_conf_line(line))
            for index, line in enumerate(lines) if self._is_ntpsec_block_begin(line)
        ]
        ends = [
            (index, self._strip_ntp_conf_line(line))
            for index, line in enumerate(lines) if self._is_ntpsec_block_end(line)
        ]
        if not begins and not ends:
            if allow_absent:
                return None, None
            raise ValueError("NTPsec managed block not found")
        if len(begins) != 1 or len(ends) != 1:
            raise ValueError("Malformed NTPsec managed block markers")
        start, begin_tag = begins[0]
        end, end_tag = ends[0]
        if end <= start or self._NTPSEC_MARKER_PAIRS[begin_tag] != end_tag:
            raise ValueError("Malformed NTPsec managed block markers")
        return start, end

    def _render_ntpsec_change(self, original, action, targets):
        lines = original.splitlines(keepends=True)
        start, end = self._parse_ntpsec_managed_block(lines)
        normalized = []
        for target in targets:
            target = self._normalize_ntp_target(target)
            if target and target not in normalized:
                normalized.append(target)
        all_targets = set()
        for line in lines[start + 1:end]:
            stripped = self._strip_ntp_conf_line(line)
            if not stripped or stripped.startswith("#"):
                continue
            match = re.match(r"^(server|pool)\s+(\S+)", stripped)
            if match:
                all_targets.add(match.group(2))
        newline = "\r\n" if "\r\n" in original else "\n"

        if action == "add":
            additions = [target for target in normalized if target not in all_targets]
            if not additions:
                return original, False
            peer_lines = ["server {} iburst{}".format(target, newline) for target in additions]
            lines[end:end] = peer_lines
            return "".join(lines), True

        block = lines[start + 1:end]
        if action == "unset":
            target_set = set(normalized)
            changed = False
            kept = []
            for line in block:
                match = re.match(r"^\s*(server|pool)\s+(\S+)", line)
                if match and match.group(2) in target_set:
                    changed = True
                    continue
                kept.append(line)
            if not changed:
                return original, False
            lines[start + 1:end] = kept
            return "".join(lines), True

        # replace: preserve every non-peer line in the managed block.
        kept = []
        insert_at = None
        for line in block:
            if re.match(r"^\s*(server|pool)\s+\S+", line):
                if insert_at is None:
                    insert_at = len(kept)
                continue
            kept.append(line)
        if insert_at is None:
            insert_at = len(kept)
        kept[insert_at:insert_at] = [
            "server {} iburst{}".format(target, newline) for target in normalized
        ]
        lines[start + 1:end] = kept
        rendered = "".join(lines)
        return rendered, rendered != original

    def _commit_ntpsec_text(self, original, updated):
        if updated == original:
            return False
        try:
            _atomic_replace_text_file(NTPSEC_CONFIG_PATH, updated)
        except Exception as exc:
            print("Failed to update NTP configuration: {}".format(exc))
            return False
        if self._restart_ntp_service(NTPSEC_SERVICE):
            return True
        try:
            _atomic_replace_text_file(NTPSEC_CONFIG_PATH, original)
        except Exception as exc:
            print(
                "CRITICAL: Failed to restore NTP configuration: {} "
                "Manual recovery is required.".format(exc)
            )
            return False
        if not self._restart_ntp_service(NTPSEC_SERVICE):
            print(
                "NTPsec restart failed after restoring the original configuration. "
                "Run 'sudo -n systemctl restart {}' manually.".format(NTPSEC_SERVICE)
            )
        return False

    def _normalize_ntp_target(self, target_raw):
        target = target_raw.strip().replace('\r', '')
        match = re.match(r"^(server|pool)\s+(.+)$", target, re.IGNORECASE)
        if match:
            target = match.group(2).strip()
        return target

    def _is_valid_ntp_target(self, target):
        if not target:
            return False
        if self.valid_ipv4_address(target):
            return True
        if re.fullmatch(r"[\d.]+", target):
            return False
        return self.is_valid_hostname(target)

    def _parse_ntpq_output(self, output):
        peers = []
        warnings = []
        reachable = False
        for line in output.splitlines():
            line_stripped = line.strip()
            if not line_stripped or line_stripped.lower().startswith("remote") or line_stripped.startswith("="):
                continue
            tokens = line_stripped.split()
            if len(tokens) < 7:
                continue
            remote = tokens[0]
            if remote and remote[0] in "*+o#x.-?":
                remote = remote[1:]
            refid = tokens[1]
            st = tokens[2]
            reach = tokens[6]
            peers.append((remote, refid, st, reach))
            reach_int = None
            if reach.isdigit():
                try:
                    reach_int = int(reach, 8)
                except Exception:
                    reach_int = None
            if reach_int is not None and reach_int > 0:
                reachable = True
            if reach_int == 0 or st == "16" or refid == ".DNS.":
                warnings.append("warning: peer {} reach={} st={} refid={}".format(remote, reach, st, refid))
        return peers, reachable, warnings

    def _restart_ntp_service(self, service_name):
        proc = subprocess.run(
            ["sudo", "-n", "systemctl", "restart", service_name],
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            print("Failed to restart NTP service: {}".format(service_name))
            print("Check sudo NOPASSWD for: systemctl restart {}".format(service_name))
            return False
        return True

    def show_dns_callback(self, key, param):
        """Show DNS servers from the canonical management stanza only."""
        try:
            text = self._read_text_exact(MGT_CONFIG_PATH)
            lines, start, end = self._mgt_static_stanza_bounds(text)
            dns = []
            for line in lines[start + 1:end]:
                match = re.match(r"^\s*dns-nameservers\s+(.+?)(?:\r?\n)?$", line)
                if match:
                    dns.extend(match.group(1).split())
            if dns:
                output = "Management DNS servers:\n"
                output += "".join("  {}\n".format(item) for item in dns)
                output += "Configuration source:\n  {}".format(MGT_CONFIG_PATH)
            else:
                output = "No DNS servers configured for mgt"
            status = 0
        except Exception as e:
            output = "\nFailed to get DNS servers: {}\n".format(e)
            status = 1
        print(output)
        return status, output

    def show_acl_callback(self, key, param):
        """
        NEW:
          show acl

        Shows:
          - policy summary (mode/iface/iface_ip)
          - AELLA_INPUT_CHAIN rules in real order (only AELLA_ACL + default tail)
        """
        state = self._load_acl_state()
        if not state:
            output = "\nACL policy is not initialized. Run 'set acl policy' first.\n"
            print(output)
            return 1, output

        iface = state["iface"]
        try:
            iface_ip = self._get_iface_ipv4(iface)
        except Exception:
            iface_ip = "(unknown)"

        output = "\n" + "=" * 60 + "\n"
        output += "Access Control List (AELLA managed)\n"
        output += "=" * 60 + "\n"
        output += f"mode : {state['mode']}\n"
        output += f"iface: {iface}\n"
        output += f"iface_ip: {iface_ip}\n\n"

        if not self._iptables_chain_exists(AELLA_INPUT_CHAIN):
            output += "No applied ACL chain found. (No rules applied yet)\n\n"
            print(output)
            return 0, output

        rc, out, err = self._run_cmd(f"sudo iptables -S {AELLA_INPUT_CHAIN}")
        if rc != 0:
            output += "Failed to get iptables rules: {}\n\n".format(err.strip() or "Unknown error")
            print(output)
            return 1, output

        lines = out.splitlines() if out else []
        shown = 0
        for line in lines:
            if not line.startswith(f"-A {AELLA_INPUT_CHAIN}"):
                continue
            if ACL_COMMENT_PREFIX.strip() in line:
                shown += 1
                output += f"  {line}\n"
                continue
            if AELLA_DEFAULT_WHITELIST_COMMENT in line or AELLA_DEFAULT_BLACKLIST_COMMENT in line:
                shown += 1
                output += f"  {line}\n"

        if shown == 0:
            output += "  (No AELLA ACL rules found in chain)\n"
        output += "\n"
        print(output)
        return 0, output

    def is_sensor_host_mode(self):
        """Detect whether this host is a Sensor KVM host without invoking a shell."""
        if os.path.exists("/sys/class/net/br-data"):
            return True
        proc = subprocess.run(
            ["virsh", "list", "--all", "--name"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, check=False,
        )
        if proc.returncode == 0:
            return any(re.search(r"\b(?:mds|mds2)\b", name) for name in proc.stdout.splitlines())
        return False

    def list_host_nics(self):
        """Return a filtered list of host NIC/bridge names."""
        nics = []
        try:
            for i in os.listdir('/sys/class/net/'):
                if i == 'lo':
                    continue
                # Filter obvious virtual/ephemeral interfaces; keep physical + intentional bridges
                if re.match(r'^(vnet|tap|tun|docker|cni|flannel|kube|wg|zt|tailscale)', i):
                    continue
                nics.append(i)
        except Exception:
            pass
        return sorted(set(nics))

    def show_gateway_sensor(self):
        """Show gateway info for Sensor host using the main routing table."""
        try:
            proc = subprocess.run(
                ["ip", "route", "show", "default"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if proc.returncode == 0 and proc.stdout.strip():
                print("\nHost default gateway(s):")
                for line in proc.stdout.splitlines():
                    print("  " + line)
                print("")
            else:
                print("\nHost default gateway is not configured or applied\n")
        except Exception as exc:
            print("Failed to get host gateway: {}".format(exc))

    def show_interface_sensor(self, param):
        """Show host NIC details for Sensor host using argv-only commands."""
        if not param:
            rc, output, _ = self._run_cmd(["ip", "-br", "addr", "show"])
            if rc == 0:
                print(output)
            print("")
            return
        iface = param[0].rstrip("?")
        if param[0].endswith("?") or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", iface):
            print("\n<Interface Name>  Specify an existing host interface/bridge name\n")
            return
        if not self.is_device_exist(iface):
            return
        for command in (["ifconfig", iface], ["ip", "link", "show", "dev", iface], ["ethtool", iface]):
            rc, output, _ = self._run_cmd(command)
            if rc == 0 and output:
                print(output.rstrip() + "\n")
        rc, link_output, _ = self._run_cmd(["ip", "link", "show", "dev", iface])
        state_match = re.search(r"\bstate\s+(\w+)", link_output)
        if state_match:
            print("Link state: {}\n".format(state_match.group(1)))
        rc, driver_output, _ = self._run_cmd(["ethtool", "-i", iface])
        if rc == 0:
            for line in driver_output.splitlines():
                if re.match(r"^(driver|version|firmware-version|bus-info):", line):
                    print(line)
            print("")

    def set_interface_sensor(self, param):
        """Reject host network changes in Sensor bridge mode."""
        self._debug_print("DEBUG set interface param={}".format(param))
        param = [p for p in param if p != '']
        if not param or len(param) < 1:
            print('\n<Interface Name>  Specify an existing host interface/bridge name\n')
            return

        interface = param[0].rstrip('?')
        if param[0].endswith('?') or interface == '?':
            print('\n<Interface Name>  Specify an existing host interface/bridge name\n')
            return

        print(
            "Host IP configuration is not managed by this CLI in Sensor bridge mode.\n"
            "Configure the Sensor VM management IP inside the Sensor VM."
        )
        return


    def unset_interface_sensor(self, param):
        """Reject host network removals in Sensor bridge mode."""
        param = [p for p in param if p != ""]
        if not param or param[0].endswith("?") or param[0] == "?":
            print("\n<Interface Name>  Specify an existing host interface/bridge name\n")
            return
        print(
            "Host IP configuration is not managed by this CLI in Sensor bridge mode.\n"
            "Configure the Sensor VM management IP inside the Sensor VM."
        )

    def show_gateway_callback(self, key, param):
        try:
            text = self._read_text_exact(MGT_CONFIG_PATH)
            lines, start, end = self._mgt_static_stanza_bounds(text)
            gateway = None
            for line in lines[start + 1:end]:
                match = re.match(r"^\s*gateway\s+(\S+)", line)
                if match:
                    gateway = match.group(1)
                    break
            print("\nConfigured management gateway: {}".format(gateway or "(none)"))
            runtime = subprocess.run(
                ["ip", "-4", "route", "show", "table", "main", "default"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if runtime.returncode == 0 and runtime.stdout.strip():
                print("Runtime main-table default: {}".format(runtime.stdout.strip()))
            print("")
        except Exception as exc:
            print("Failed to get gateway: {}".format(exc))

    def show_service(self, key, param):
        if key:
            self.shell_cmd_exec('sudo virsh list --all')

    @staticmethod
    def _parse_virsh_autostart(dominfo_text: str) -> Optional[bool]:
        for line in dominfo_text.splitlines():
            if line.lower().startswith("autostart:"):
                raw_value = line.split(":", 1)[1].strip().lower()
                if raw_value in {"enable", "enabled", "yes", "on", "1"}:
                    return True
                if raw_value in {"disable", "disabled", "no", "off", "0"}:
                    return False
                return None
        return None

    def show_autostart_callback(self, key, param):
        """Show VM auto start configuration."""
        vm_list = self.get_vm_list()
        if not vm_list:
            print("\nNo VMs found.\n")
            return
        print("\nVM Auto Start Configuration:")
        print("-" * 50)
        for vm in sorted(vm_list):
            if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm):
                print("  {:<20} unknown".format(vm))
                continue
            try:
                proc = subprocess.run(
                    ["virsh", "dominfo", vm],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                    check=False,
                )
                status = "unknown"
                if proc.returncode == 0:
                    parsed = self._parse_virsh_autostart(proc.stdout)
                    if parsed is True:
                        status = "enabled"
                    elif parsed is False:
                        status = "disabled"
                print("  {:<20} {}".format(vm, status))
            except Exception:
                print("  {:<20} unknown".format(vm))
        print("")

    def show_interface_callback(self, key, param):
        if param and param[0].rstrip("?") == "mgt":
            if param[0].endswith("?"):
                print("\nPress [Enter]\n")
                return
            rc, output, _ = self._run_cmd(["ifconfig", "mgt"])
            if output:
                print(output)
            return
        if self.is_sensor_host_mode():
            self.show_interface_sensor(param)
            return
        if not param:
            for iface in os.listdir("/sys/class/net/"):
                if re.match(r"^(en|eth|br0-aio|mgt|mgmt|xmgt|data1g|data10g|cltr0)", iface):
                    if self.is_device_exist(iface):
                        rc, output, _ = self._run_cmd(["ifconfig", iface])
                        if rc == 0 and output:
                            print(output)
            return
        iface = param[0].rstrip("?")
        if param[0].endswith("?") or not re.fullmatch(r"(?:mgt|data1g|data10g|cltr0)", iface):
            print("\n<Interface Name>  Specify a supported interface name (mgt, data1g, data10g, cltr0)")
            print("Press [Enter]\n")
            return
        if len(param) > 1:
            if len(param) == 2 and param[1] == "?":
                print("\nPress [Enter]\n")
            else:
                print("Invalid interface command.")
            return
        if not self.is_device_exist(iface):
            return
        for command in (["ifconfig", iface], ["ip", "link", "show", "dev", iface], ["ethtool", iface]):
            rc, output, _ = self._run_cmd(command)
            if rc == 0 and output:
                print(output.rstrip() + "\n")
        if iface == "cltr0":
            rc, output, _ = self._run_cmd(["ip", "link", "show", "dev", iface])
            if output:
                print(output.rstrip() + "\n")
        rc, driver_output, _ = self._run_cmd(["ethtool", "-i", iface])
        if rc == 0:
            for line in driver_output.splitlines():
                if re.match(r"^(driver|version|firmware-version|bus-info):", line):
                    print(line)
            print("")

    def show_route_callback(self, key, param):
        """Show routing tables without a shell."""
        for table, title in (
            ("main", "Main routing table"),
            ("1", "Management network routing table (table 1)"),
            ("2", "Data network routing table (table 2)"),
        ):
            print("\n" + "-" * 87)
            print(title)
            print("-" * 87)
            rc, output, err = self._run_cmd(["ip", "route", "show", "table", table])
            if rc == 0 and output.strip():
                print(output.rstrip())
            else:
                print("N/A")
                if err.strip():
                    print(err.strip())

    def show_cli_callback(self, key, param):
        last = 30
        if not param or param[0].rstrip("?") != "history":
            print("\nhistory    Show CLI history\n")
            return
        if len(param) == 1 or (len(param) == 2 and param[1] == "?"):
            pass
        elif len(param) == 3 and param[1].rstrip("?") == "last":
            try:
                last = int(param[2])
            except (TypeError, ValueError):
                print("Invalid number: Enter a valid number from 1 to 5000\n")
                return
            if not 1 <= last <= 5000:
                print("Invalid number: Enter a valid number from 1 to 5000\n")
                return
        else:
            print('\nUsage: show cli history [last <1..5000>]\n')
            return

        log_path = Path(LOG_DIR) / "aella_cli.log"
        try:
            if os.geteuid() == 0:
                content = _read_root_text_file(log_path)
            else:
                content = log_path.read_text(encoding="utf-8", errors="replace")
        except OSError:
            print("No CLI history is available.\n")
            return
        except Exception as exc:
            print("Unable to read CLI history: {}\n".format(exc))
            return

        records = []
        for line in content.splitlines()[-last:]:
            fields = line.split("|", 4)
            if len(fields) < 5 or "Run command:" not in fields[4]:
                continue
            timestamp = fields[0].split(",", 1)[0]
            command_text = fields[4].split("Run command:", 1)[1].strip()
            records.append((timestamp, command_text))
        for timestamp, command_text in sorted(records, reverse=True):
            print("{} {}".format(timestamp, command_text))

    # Set command
    @log_cmd
    def do_set(self, line):
        """ Set command """
        return self._on_nested_command(line, self.set_command_help, self.set_command_callback)

    @staticmethod
    def set_password_callback(key, param):
        if len(param) > 0:
            print('\nset password <Enter>\t Press enter to input password and ctrl-D to abort\n')
            return

        invoking_user = _get_invoking_username() or ""
        if invoking_user in {"aella", "stellar"}:
            try:
                pwd.getpwnam(invoking_user)
                username = invoking_user
            except KeyError:
                username = ""
        else:
            username = ""

        if not username:
            for candidate in ("aella", "stellar"):
                try:
                    pwd.getpwnam(candidate)
                    username = candidate
                    break
                except KeyError:
                    continue

        if not username:
            print("No supported appliance account (aella/stellar) was found.")
            return
        subprocess.call(["/usr/bin/passwd", username])

    def set_tz_callback(self, key, param):
        timezones = self._list_timezones()
        if not timezones:
            print("Failed to list timezones")
            return

        if len(param) == 0:
            regions = sorted({tz.split("/", 1)[0] if "/" in tz else tz for tz in timezones})
            print("\nAvailable regions:\n")
            for region in regions:
                print(region)
            print("\nExamples:")
            print("  set timezone Asia")
            print("  set timezone Asia/Seoul")
            print("  set timezone \"America/Los_Angeles\"\n")
            return

        tz_raw = " ".join(param).strip()
        tz = tz_raw
        if len(tz) >= 2 and tz[0] == tz[-1] and tz[0] in ("'", '"'):
            tz = tz[1:-1].strip()

        regions = {tz_item.split("/", 1)[0] if "/" in tz_item else tz_item for tz_item in timezones}

        if tz in timezones:
            proc = subprocess.run(
                ["sudo", "timedatectl", "set-timezone", tz],
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            if proc.returncode != 0:
                err = proc.stderr.strip() if proc.stderr else "Unknown error"
                print("Failed to set timezone: {}".format(err))
            return

        if tz in regions and "/" not in tz:
            candidates = [t for t in timezones if t.startswith(tz + "/")]
            priority_terms = ["Seoul", "Tokyo", "New_York", "Los_Angeles"]

            def _tz_sort_key(value: str) -> tuple[int, str]:
                for term in priority_terms:
                    if term in value:
                        return (0, value)
                return (1, value)

            candidates = sorted(candidates, key=_tz_sort_key)
            limit = 50
            print("\nAvailable timezones for {}:\n".format(tz))
            for item in candidates[:limit]:
                print(item)
            remaining = len(candidates) - limit
            if remaining > 0:
                print("... ({} more)".format(remaining))
            print("\nPick one: set timezone <Region/City>\n")
            return

        print("Unknown timezone: {}".format(tz))
        print("Unknown timezone. e.g.: 'America/Los_Angeles'")
        print("Try: set timezone <Region>  (to list options)")
        suggestions = []
        for item in timezones:
            if item.startswith(tz):
                suggestions.append(item)
        for item in timezones:
            if tz in item and item not in suggestions:
                suggestions.append(item)
        if suggestions:
            print("Suggestions:")
            for item in suggestions[:5]:
                print("  {}".format(item))
        return

    def set_time_callback(self, key, param):
        if not param or len(param) != 2 or param[0].endswith('?') or param[1].endswith('?'):
            print('\n<YYYY-MM-DD HH:MM:SS> \t Specify system date and time\n')
            return

        date, time = param
        if not re.fullmatch(r"\d{4}-\d{2}-\d{2}", date):
            print('Wrong date format:', date)
            return
        if not re.fullmatch(r"\d{2}:\d{2}:\d{2}", time):
            print('Wrong time format:', time)
            return
        try:
            timestamp = datetime.datetime.strptime(
                "{} {}".format(date, time), "%Y-%m-%d %H:%M:%S"
            ).strftime("%Y-%m-%d %H:%M:%S")
        except ValueError:
            print("Wrong date or time value.")
            return

        success, output = self.run_command_with_stderr(["sudo", "date", "-s", timestamp])
        if success:
            if output:
                print(output.decode("utf-8", errors="replace").strip() if isinstance(output, bytes) else str(output).strip())
        else:
            message = output.decode("utf-8", errors="replace").strip() if isinstance(output, bytes) else str(output)
            print("Failed to set system time: {}".format(message))

    def _detect_ntp_type(self):
        """Validate that the supported NTPsec backend is usable."""
        error = "NTPsec is not installed or /etc/ntpsec/ntp.conf is missing."
        if not os.path.isfile(NTPSEC_CONFIG_PATH):
            raise RuntimeError(error)
        service = subprocess.run(
            ["systemctl", "cat", NTPSEC_SERVICE],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
        )
        if service.returncode != 0:
            raise RuntimeError(error)
        if not shutil.which(NTPSEC_QUERY_COMMAND[0]):
            raise RuntimeError(error)
        query = subprocess.run(
            NTPSEC_QUERY_COMMAND,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
        )
        if query.returncode not in (0, 1):
            raise RuntimeError(error)
        return "ntpsec", NTPSEC_CONFIG_PATH, NTPSEC_SERVICE

    def set_dns_callback(self, key, param):
        """Configure DNS servers for a network interface"""
        if not param or param[0].endswith('?') or len(param) < 2:
            print('\n<Interface Name> <DNS IP> [...]  Specify interface name and DNS server IP address(es)\n')
            print('Example: set dns mgt 8.8.8.8 8.8.4.4\n')
            return
        
        interface = param[0].rstrip('?')
        if param[0].endswith('?') or interface == '?':
            print('\n<Interface Name> <DNS IP> [...]  Specify interface name and DNS server IP address(es)\n')
            return
        if interface != "mgt":
            print('Invalid option: Only "mgt" interface supports DNS configuration')
            return
        
        # Validate DNS IP addresses
        dns_servers = param[1:]
        for dns in dns_servers:
            if not self.valid_ipv4_address(dns):
                print('Invalid DNS server IP address format: {}\n'.format(dns))
                return
        
        if self._update_mgt_ipv4_config(dns_servers=dns_servers):
            if self._mgt_last_changed:
                print("Configuration updated successfully.")
                print("Run 'set interface mgt restart' to apply the changes.")

    def _ntpsec_operation(self, action, targets):
        try:
            self._detect_ntp_type()
            original = self._read_text_exact(NTPSEC_CONFIG_PATH)
            updated, changed = self._render_ntpsec_change(original, action, targets)
        except Exception as exc:
            print("Failed to update NTP configuration: {}".format(exc))
            return False
        if not changed:
            if action == "unset":
                print("NTP server not found in CLI-managed block")
            else:
                print("NTP configuration is unchanged")
            return False
        if not self._commit_ntpsec_text(original, updated):
            return False
        query = subprocess.run(
            NTPSEC_QUERY_COMMAND,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
        )
        if query.returncode == 0:
            peers, _, _ = self._parse_ntpq_output(query.stdout)
            reach_zero = False
            for peer in peers:
                try:
                    if int(peer[3], 8) == 0:
                        reach_zero = True
                        break
                except (TypeError, ValueError):
                    continue
            if reach_zero:
                print("Warning: NTP peers currently have reach=0")
        return True

    def set_ntp_callback(self, key, param):
        if not param or param[0].endswith("?"):
            print("\n<NTP server> \t Specify NTP server name or IP address\n")
            return
        action = "add"
        targets = list(param)
        if param[0] in ("add", "replace"):
            action = param[0]
            targets = param[1:]
        if not targets:
            print("\n<NTP server> \t Specify NTP server name or IP address\n")
            return
        targets = [self._normalize_ntp_target(target) for target in targets]
        if any(not self._is_valid_ntp_target(target) for target in targets):
            print("Invalid NTP hostname: Please enter the correct hostname")
            return
        if self._ntpsec_operation(action, targets):
            if action == "replace":
                print("Successfully replaced ntp servers\n")
            else:
                print("Successfully set ntp servers\n")
            return 0
        return 1

    def show_ntp_callback(self, key, param):
        try:
            self._detect_ntp_type()
            lines = self._read_text_exact(NTPSEC_CONFIG_PATH).splitlines(keepends=True)
            start, end = self._parse_ntpsec_managed_block(lines)
            entries = []
            if start is not None:
                for line in lines[start + 1:end]:
                    match = re.match(r"^\s*(server|pool)\s+(\S+)", line)
                    if match:
                        entries.append("{} {}".format(match.group(1), match.group(2)))
            active = subprocess.run(
                ["systemctl", "is-active", NTPSEC_SERVICE],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            enabled = subprocess.run(
                ["systemctl", "is-enabled", NTPSEC_SERVICE],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            query = subprocess.run(
                NTPSEC_QUERY_COMMAND,
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            output = "\n[configured NTP servers - CLI managed]\n"
            output += "".join("- {}\n".format(entry) for entry in entries) or "(none)\n"
            output += "\n[service]\n- {}: {} ({})\n".format(
                NTPSEC_SERVICE,
                active.stdout.strip() if active.returncode == 0 else "inactive",
                enabled.stdout.strip() if enabled.returncode == 0 else "disabled",
            )
            output += "\n[runtime sync status]\n"
            output += query.stdout if query.returncode == 0 else "(ntpq query failed)\n"
            print(output)
            return 0, output
        except Exception as exc:
            output = "Failed to get ntp servers: {}\n".format(exc)
            print(output)
            return 1, output

    def _get_local_interface_ips(self):
        """Return only the approved always-allow destination IPs"""
        return list(ALWAYS_ALLOW_DEST_IPS)

    def get_ipv4_addrs(self, iface: str) -> list[str]:
        """Return IPv4 addresses for an interface"""
        cmd = ["ip", "-4", "-o", "addr", "show", "dev", iface]
        proc = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
        if proc.returncode != 0 or not proc.stdout:
            return []
        addrs = []
        for line in proc.stdout.splitlines():
            match = re.search(r"\binet\s+(\d+\.\d+\.\d+\.\d+)/", line)
            if match:
                addrs.append(match.group(1))
        return addrs

    def list_candidate_ifaces(self, exclude_ips: Sequence[str] = ACL_EXCLUDE_IPS) -> list[dict]:
        """Return candidate interfaces with IPv4 list, excluding any in ACL_EXCLUDE_IPS"""
        if isinstance(exclude_ips, str):
            exclude_set = {exclude_ips}
        else:
            exclude_set = set(exclude_ips)
        candidates = []
        for iface in self.list_host_nics():
            ipv4s = self.get_ipv4_addrs(iface)
            if not ipv4s:
                continue
            if exclude_set.intersection(ipv4s):
                continue
            candidates.append({"iface": iface, "ipv4": ipv4s})
        return candidates

    def _load_acl_state(self) -> dict:
        """Load ACL policy state"""
        default_data = {"mode": None, "iface": None, "exclude_ip": list(ACL_EXCLUDE_IPS)}
        try:
            with open(ACL_STATE_PATH, "r") as f:
                data = json.load(f)
        except FileNotFoundError:
            return default_data
        except PermissionError:
            proc = subprocess.run(
                ["sudo", "cat", ACL_STATE_PATH],
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                text=True,
                check=False,
            )
            if proc.returncode != 0 or not proc.stdout:
                return default_data
            try:
                data = json.loads(proc.stdout)
            except json.JSONDecodeError:
                return default_data
        except json.JSONDecodeError:
            return default_data
        except Exception:
            return default_data

        if not isinstance(data, dict):
            return default_data
        if "mode" not in data or "iface" not in data:
            return default_data
        if "exclude_ip" not in data:
            data["exclude_ip"] = list(ACL_EXCLUDE_IPS)
        return data

    def load_acl_state(self) -> dict:
        return self._load_acl_state()

    def _save_acl_state(self, data: dict) -> None:
        _ensure_root_owned_directory("/var/lib/aella", mode=0o750)
        _write_root_text_file(ACL_STATE_PATH, json.dumps(data, indent=2, sort_keys=False))

    def _clear_acl_state(self) -> None:
        _ensure_root_owned_directory("/var/lib/aella", mode=0o750)
        if os.path.lexists(ACL_STATE_PATH):
            os.unlink(ACL_STATE_PATH)

    def _get_iface_ipv4(self, iface: str) -> str:
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", iface or ""):
            raise RuntimeError("Invalid interface name")
        rc, out, err = self._run_cmd(["ip", "-4", "addr", "show", "dev", iface])
        if rc != 0 or not out:
            raise RuntimeError("Failed to get IPv4 for iface={}: {}".format(iface, err.strip()))
        match = re.search(r"\binet\s+(\d+\.\d+\.\d+\.\d+)/", out)
        if not match:
            raise RuntimeError("No IPv4 found on iface={}".format(iface))
        return match.group(1)

    def _iptables_chain_exists(self, chain: str) -> bool:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", chain or ""):
            return False
        rc, _, _ = self._run_cmd(["sudo", "iptables", "-S", chain])
        return rc == 0

    def _iptables_ensure_chain(self, chain: str) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", chain or ""):
            raise ValueError("Invalid iptables chain name")
        if not self._iptables_chain_exists(chain):
            rc, _, err = self._run_cmd(["sudo", "iptables", "-N", chain])
            if rc != 0:
                raise RuntimeError("Failed to create iptables chain {}: {}".format(chain, err.strip()))

    def _iptables_flush_chain(self, chain: str) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", chain or ""):
            raise ValueError("Invalid iptables chain name")
        rc, _, err = self._run_cmd(["sudo", "iptables", "-F", chain])
        if rc != 0:
            raise RuntimeError("Failed to flush iptables chain {}: {}".format(chain, err.strip()))

    def _iptables_delete_chain(self, chain: str) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", chain or ""):
            raise ValueError("Invalid iptables chain name")
        if self._iptables_chain_exists(chain):
            self._run_cmd(["sudo", "iptables", "-F", chain])
            self._run_cmd(["sudo", "iptables", "-X", chain])

    def _iptables_rule_check(self, table_chain, rule_args):
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", table_chain or ""):
            return False
        try:
            args = shlex.split(rule_args) if isinstance(rule_args, str) else list(rule_args)
        except (TypeError, ValueError):
            return False
        rc, _, _ = self._run_cmd(["sudo", "iptables", "-C", table_chain] + args)
        return rc == 0

    def _iptables_rule_insert(self, table_chain: str, position: int | None, rule_args) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", table_chain or ""):
            raise ValueError("Invalid iptables chain name")
        args = shlex.split(rule_args) if isinstance(rule_args, str) else list(rule_args)
        command = ["sudo", "iptables"]
        if position is None:
            command.extend(["-A", table_chain])
        else:
            if not isinstance(position, int) or position < 1:
                raise ValueError("Invalid iptables rule position")
            command.extend(["-I", table_chain, str(position)])
        command.extend(args)
        rc, _, err = self._run_cmd(command)
        if rc != 0:
            raise RuntimeError("Failed to insert iptables rule: {}".format(err.strip()))

    def _iptables_rule_delete(self, table_chain: str, rule_args) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_]{1,28}", table_chain or ""):
            raise ValueError("Invalid iptables chain name")
        args = shlex.split(rule_args) if isinstance(rule_args, str) else list(rule_args)
        rc, _, err = self._run_cmd(["sudo", "iptables", "-D", table_chain] + args)
        if rc != 0:
            raise RuntimeError("Failed to delete iptables rule: {}".format(err.strip()))

    def _ensure_aella_system_rules(self, iface: str) -> None:
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", iface or ""):
            raise ValueError("Invalid ACL interface")
        self._iptables_ensure_chain(AELLA_INPUT_CHAIN)
        established = [
            "-m", "conntrack", "--ctstate", "ESTABLISHED,RELATED",
            "-j", "ACCEPT", "-m", "comment", "--comment",
            AELLA_SYSTEM_ALLOW_ESTABLISHED_COMMENT,
        ]
        if not self._iptables_rule_check("INPUT", established):
            self._iptables_rule_insert("INPUT", 1, established)
        jump = [
            "-i", iface, "-j", AELLA_INPUT_CHAIN,
            "-m", "comment", "--comment", AELLA_SYSTEM_JUMP_COMMENT,
        ]
        if not self._iptables_rule_check("INPUT", jump):
            self._iptables_rule_insert("INPUT", 2, jump)

    def _remove_aella_system_rules(self) -> None:
        rc, output, _ = self._run_cmd(["sudo", "iptables", "-S", "INPUT"])
        if rc == 0:
            for line in output.splitlines():
                if not line.startswith("-A INPUT"):
                    continue
                if AELLA_SYSTEM_JUMP_COMMENT not in line and AELLA_SYSTEM_ALLOW_ESTABLISHED_COMMENT not in line:
                    continue
                try:
                    tokens = shlex.split(line)
                except ValueError:
                    continue
                if len(tokens) >= 2 and tokens[:2] == ["-A", "INPUT"]:
                    tokens[0] = "-D"
                    self._run_cmd(["sudo", "iptables"] + tokens)
        self._iptables_delete_chain(AELLA_INPUT_CHAIN)

    def _build_user_rule_args(self, iface: str, iface_ip: str, action: str, source: str, port: str, desc: str) -> list[str]:
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", iface or ""):
            raise ValueError("Invalid ACL interface")
        iface_ip = str(ipaddress.IPv4Address(iface_ip))
        if action not in {"allow", "deny"}:
            raise ValueError("Invalid ACL action")
        if source not in ("0.0.0.0/0", "0.0.0.0"):
            source = str(ipaddress.ip_network(source, strict=False))
        if port not in {"all", "icmp", "ping"}:
            if not str(port).isdigit() or not 1 <= int(port) <= 65535:
                raise ValueError("Invalid ACL port")
            port = str(int(port))
        target = "ACCEPT" if action == "allow" else "DROP"
        comment_value = ACL_COMMENT_PREFIX + "".join(
            ch for ch in (desc or "") if ch.isprintable()
        )[:180]
        args = ["-i", iface]
        if source not in ("0.0.0.0/0", "0.0.0.0"):
            args.extend(["-s", source])
        args.extend(["-d", "{}/32".format(iface_ip)])
        if port in {"icmp", "ping"}:
            args.extend(["-p", "icmp", "--icmp-type", "echo-request"])
        elif port != "all":
            args.extend(["-p", "tcp", "--dport", port])
        args.extend(["-j", target, "-m", "comment", "--comment", comment_value])
        return args

    def _normalize_acl_source(self, source: str | None) -> str | None:
        if not source:
            return None
        if source in ("0.0.0.0/0", "0.0.0.0"):
            return None
        if "/" not in source:
            return f"{source}/32"
        return source

    def _port_to_proto_dport(self, port: str) -> tuple[str | None, str | None]:
        if port == "all":
            return (None, None)
        if port in ("icmp", "ping"):
            return ("icmp", None)
        return ("tcp", str(port))

    def _user_rule_exists_in_chain(self, chain_rules: list[dict], action: str, source: str, port: str) -> bool:
        target = "ACCEPT" if action == "allow" else "DROP"
        src_norm = self._normalize_acl_source(source)
        proto, dport = self._port_to_proto_dport(port)
        for rule in chain_rules:
            if rule.get("target") != target:
                continue
            rule_src = rule.get("src")
            if src_norm is None:
                if rule_src not in (None, "0.0.0.0/0", "0.0.0.0"):
                    continue
            else:
                if rule_src != src_norm:
                    continue
            if proto is None:
                if rule.get("proto") is not None:
                    continue
            else:
                if rule.get("proto") != proto:
                    continue
            if dport is None:
                if rule.get("dport") is not None:
                    continue
            else:
                if rule.get("dport") != dport:
                    continue
            return True
        return False

    def _append_user_rule_summary(self, chain_rules: list[dict], action: str, source: str, port: str) -> None:
        target = "ACCEPT" if action == "allow" else "DROP"
        src_norm = self._normalize_acl_source(source)
        proto, dport = self._port_to_proto_dport(port)
        chain_rules.append(
            {
                "raw": "",
                "src": src_norm,
                "proto": proto,
                "dport": dport,
                "target": target,
                "comment": None,
            }
        )

    def _ensure_default_tail_rule_last(self, mode: str, iface_ip: str) -> None:
        iface_ip = str(ipaddress.IPv4Address(iface_ip))
        _, parsed = self.parse_chain_rules(AELLA_INPUT_CHAIN)
        for rule in parsed:
            if self._comment_is_default_tail(rule.get("comment")):
                self._delete_chain_rule_line(rule["raw"])
        if mode == "whitelist":
            target = "DROP"
            comment = AELLA_DEFAULT_WHITELIST_COMMENT
        elif mode == "blacklist":
            target = "ACCEPT"
            comment = AELLA_DEFAULT_BLACKLIST_COMMENT
        else:
            raise ValueError("Invalid ACL mode")
        self._run_iptables(
            ["-A", AELLA_INPUT_CHAIN, "-d", "{}/32".format(iface_ip),
             "-j", target, "-m", "comment", "--comment", comment],
            "Failed to ensure default ACL rule",
        )

    def _stage_rule(self, action, source, ports, desc):
        """Stage a rule in ACL staging file, avoid duplicates"""
        data = self._load_acl_staging()
        rules = data.get("rules", [])
        staged_rule = {
            "action": action,
            "source": source,
            "ports": ports,
            "desc": desc or "",
        }
        for rule in rules:
            if rule.get("action") == staged_rule["action"] and rule.get("source") == staged_rule["source"] and rule.get("ports") == staged_rule["ports"]:
                return False
        rules.append(staged_rule)
        data["rules"] = rules
        self._save_acl_staging(data)
        return True

    def _iptables_add(self, action, source, ports, desc, dest_ip=None):
        if action not in {"allow", "deny"}:
            raise ValueError("Invalid ACL action")
        if not dest_ip:
            dest_ip = self._get_mgt_ipv4()
        dest_ip = str(ipaddress.IPv4Address(dest_ip))
        if source not in ("0.0.0.0/0", "0.0.0.0"):
            source = str(ipaddress.ip_network(source, strict=False))
        target = "ACCEPT" if action == "allow" else "DROP"
        comment_value = ACL_COMMENT_PREFIX + "".join(ch for ch in (desc or "") if ch.isprintable())[:180]
        for port in ports:
            args = ["sudo", "iptables", "-I", "INPUT"]
            if source not in ("0.0.0.0/0", "0.0.0.0"):
                args.extend(["-s", source])
            args.extend(["-d", "{}/32".format(dest_ip)])
            if port != "all":
                if str(port) in {"icmp", "ping"}:
                    args.extend(["-p", "icmp"])
                elif str(port).isdigit() and 1 <= int(port) <= 65535:
                    args.extend(["-p", "tcp", "--dport", str(int(port))])
                else:
                    raise ValueError("Invalid ACL port")
            args.extend(["-m", "comment", "--comment", comment_value, "-j", target])
            subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)

    def _iptables_rule_exists(self, action, source, port, dest_ip=None):
        if action not in {"allow", "deny"}:
            return False
        if not dest_ip:
            dest_ip = self._get_mgt_ipv4()
        try:
            dest_ip = str(ipaddress.IPv4Address(dest_ip))
            if source not in ("0.0.0.0/0", "0.0.0.0"):
                source = str(ipaddress.ip_network(source, strict=False))
        except ValueError:
            return False
        target = "ACCEPT" if action == "allow" else "DROP"
        args = ["sudo", "iptables", "-C", "INPUT", "-d", "{}/32".format(dest_ip)]
        if port != "all":
            if str(port) in {"icmp", "ping"}:
                args.extend(["-p", "icmp"])
            elif str(port).isdigit() and 1 <= int(port) <= 65535:
                args.extend(["-p", "tcp", "--dport", str(int(port))])
            else:
                return False
        args.extend(["-j", target])
        if source not in ("0.0.0.0/0", "0.0.0.0"):
            args.extend(["-s", source])
        proc = subprocess.run(args, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        return proc.returncode == 0

    def _iptables_delete_user_rules(self):
        proc = subprocess.run(
            ["sudo", "iptables", "-S", "INPUT"],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
        )
        if proc.returncode != 0:
            return
        for line in proc.stdout.splitlines():
            if not line.startswith("-A INPUT"):
                continue
            try:
                tokens = shlex.split(line)
            except ValueError:
                continue
            if not any(token.startswith(ACL_COMMENT_PREFIX.strip()) for token in tokens):
                continue
            if tokens[:2] == ["-A", "INPUT"]:
                tokens[0] = "-D"
                subprocess.run(
                    ["sudo", "iptables"] + tokens,
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                )

    def set_acl_callback(self, key, param):
        """
        NEW ACL UX:

          set acl policy
          set acl <IP/network> <port|icmp|ping> [...] | all [description]
          set acl apply [--reset]

        IMPORTANT:
          - policy only sets mode/iface, DOES NOT touch iptables.
          - apply does NOTHING if staged rules are empty (no iptables changes at all).
        """
        # -----------------------
        # Helper: print usage
        # -----------------------
        def _print_usage(policy_missing: bool):
            print("")
            if policy_missing:
                print("ACL policy is not initialized.")
                print("You must run 'set acl policy' before adding or applying any ACL rules.")
                print("")
            print("------------------------------------------------------------")
            print("Required first step:")
            print("  set acl policy        Initialize ACL mode (whitelist/blacklist) and target interface")
            print("")
            print("------------------------------------------------------------")
            print("ACL rule syntax (available after policy is initialized):")
            print("  set acl <IP/network> <port|icmp|ping|all> [description]")
            print("")
            print("  IP/network : IP address (e.g., 192.168.1.100) or network (e.g., 192.168.1.0/24)")
            print("  port       : Port number (e.g., 22, 80, 443), \"icmp\"/\"ping\", or \"all\" for all ports")
            print("               Multiple ports can be specified separated by space")
            print("  description: Optional description/comment")
            print("")
            print("------------------------------------------------------------")
            print("Apply staged rules (rules must exist):")
            print("  set acl apply          Apply staged ACL rules (merge)")
            print("  set acl apply --reset  Reset applied ACL rules and rebuild from staging")
            print("")
            print("------------------------------------------------------------")
            print("Examples:")
            print("  set acl policy")
            print("  set acl 192.168.1.100 22 \"Admin SSH access\"")
            print("  set acl 192.168.1.0/24 80 443 \"Web servers\"")
            print("  set acl 10.0.0.0/8 all \"Internal network\"")
            print("  set acl apply")
            print("")

        # no args => show usage (policy-first)
        if not param:
            state = self._load_acl_state()
            _print_usage(policy_missing=(not state))
            return

        # -----------------------
        # set acl policy
        # -----------------------
        if param[0].lower() == "policy":
            warning = (
                "\nWARNING: Re-initializing ACL policy will DELETE ALL existing AELLA ACL rules (live) and staged rules.\n"
                "This action cannot be undone.\n\n"
                "Type YES to continue: "
            )
            if not self._confirm_yes(warning):
                print("\nCanceled.\n")
                return

            # destructive cleanup
            self._clear_acl_staging()
            self._clear_acl_state()
            self._remove_aella_system_rules()

            # select mode
            print("\nSelect ACL mode:")
            print("  1) whitelist  (specified sources are ALLOWED, all others are DENIED)")
            print("  2) blacklist  (specified sources are DENIED, all others are ALLOWED)")
            mode_sel = input("Enter 1 or 2: ").strip()
            if mode_sel not in ("1", "2"):
                print("\nInvalid selection. Canceled.\n")
                return
            mode = "whitelist" if mode_sel == "1" else "blacklist"

            # select iface (single)
            candidates = self._list_acl_candidate_ifaces()
            if not candidates:
                print("\nNo eligible interfaces found (IPv4 required; excluding 192.168.0.100, 192.168.122.1).\n")
                return

            print("\nSelect target interface (exactly ONE):")
            for idx, (ifn, ip) in enumerate(candidates, start=1):
                print(f"  {idx}) {ifn}  (IPv4: {ip})")
            sel = input("Enter number: ").strip()
            if not sel.isdigit() or not (1 <= int(sel) <= len(candidates)):
                print("\nInvalid selection. Canceled.\n")
                return
            iface, iface_ip = candidates[int(sel) - 1]

            self._save_acl_state({"mode": mode, "iface": iface, "iface_ip": iface_ip})
            print("\nPolicy saved.")
            print("  mode : {}".format(mode))
            print("  iface: {} (IPv4: {})".format(iface, iface_ip))
            print("\nNOTE: No firewall rules are active until at least one ACL rule is added and 'set acl apply' is executed.\n")
            return

        # -----------------------
        # set acl apply [--reset]
        # -----------------------
        if param[0].lower() == "apply":
            # policy must exist
            state = self._load_acl_state()
            if not state:
                print("\nACL policy is not initialized. Run 'set acl policy' first.\n")
                return

            # parse options
            reset = False
            tokens = param[1:]
            for t in tokens:
                if t == "--reset":
                    reset = True
                else:
                    print("\nInvalid option. Use: set acl apply [--reset]\n")
                    return

            data = self._load_acl_staging()
            rules = data.get("rules", [])
            if not rules:
                print("\nNo ACL rules defined. Nothing to apply.")
                print("Policy-only does not enforce allow/deny all. (No iptables changes were made.)\n")
                return

            # SSH risk warning (mandatory)
            mode = state["mode"]
            client_ip = self._detect_ssh_client_ip()
            if mode == "whitelist":
                risk_level, risk_msg = self._compute_whitelist_ssh_risk(client_ip, rules)
                print("\n[SSH Safety Check]")
                print(risk_msg)
                if risk_level == "HIGH":
                    if not self._confirm_yes("\nType YES to apply anyway (HIGH RISK): "):
                        print("\nCanceled. No changes applied.\n")
                        return
                else:
                    if not self._confirm_yes("\nType YES to apply: "):
                        print("\nCanceled. No changes applied.\n")
                        return
            else:
                # blacklist: still warn generally
                print("\n[SSH Safety Check]")
                if client_ip:
                    print(f"Current SSH client IP detected: {client_ip}")
                print("Applying ACL may terminate your current session depending on rules.")
                if not self._confirm_yes("\nType YES to apply: "):
                    print("\nCanceled. No changes applied.\n")
                    return

            # APPLY (rules exist -> now allowed to touch iptables)
            iface = state["iface"]
            iface_ip = self._get_iface_ipv4(iface)

            # ensure base system rules and chain/jump
            self._ensure_aella_system_rules(iface)

            if reset:
                self._iptables_flush_chain(AELLA_INPUT_CHAIN)

            # add user rules (append order)
            _, existing_rules = self.parse_chain_rules(AELLA_INPUT_CHAIN)
            for r in rules:
                action = r.get("action")
                source = r.get("source")
                ports = r.get("ports", [])
                desc = r.get("desc", "")
                if not action or not source or not ports:
                    continue
                for p in ports:
                    if self._user_rule_exists_in_chain(existing_rules, action, source, p):
                        continue
                    args = self._build_user_rule_args(iface, iface_ip, action, source, p, desc)
                    if not self._iptables_rule_check(AELLA_INPUT_CHAIN, args):
                        self._iptables_rule_insert(AELLA_INPUT_CHAIN, None, args)
                        self._append_user_rule_summary(existing_rules, action, source, p)

            # ensure default tail last
            self._ensure_default_tail_rule_last(state["mode"], iface_ip)

            # clear staging after successful apply
            self._clear_acl_staging()
            self._persist_iptables_rules()
            if reset:
                print("\nApplied staged ACL rules with reset (rebuild completed).")
            else:
                print("\nApplied staged ACL rules (merge completed).")
            print("Staging cleared.\n")
            return

        # -----------------------
        # set acl <src> <ports...|all> [desc]
        # -----------------------
        state = self._load_acl_state()
        if not state:
            print("\nACL policy is not initialized. Run 'set acl policy' first.\n")
            return

        # param[0] must be source
        source = param[0]
        # Validate IP/network
        if "/" in source:
            parts = source.split("/")
            if not self.valid_ipv4_address(parts[0]) or not parts[1].isdigit() or int(parts[1]) > 32:
                print("\nInvalid network format: Use CIDR notation (e.g., 192.168.1.0/24)\n")
                return
        else:
            if not self.valid_ipv4_address(source):
                print("\nInvalid IP address format: {}\n".format(source))
                return

        if len(param) < 2:
            print("\nPort specification required.\n")
            return

        remaining = param[1:]
        ports: list[str] = []
        description: str | None = None

        for i, p in enumerate(remaining):
            if p == "all" or p in ("icmp", "ping") or p.isdigit():
                ports.append(p)
            else:
                description = " ".join(remaining[i:])
                break

        if not ports:
            print("\nPort specification required.\n")
            return

        if "all" in ports:
            if len(ports) > 1:
                print('\nCannot specify "all" with other ports\n')
                return
            ports = ["all"]

        if ports != ["all"]:
            normalized_ports = []
            for p in ports:
                p = "icmp" if p == "ping" else p
                if p not in normalized_ports:
                    normalized_ports.append(p)
            ports = normalized_ports

        # validate ports
        if ports != ["all"]:
            for p in ports:
                if p in ("icmp", "ping"):
                    continue
                try:
                    n = int(p)
                    if n < 1 or n > 65535:
                        print("\nInvalid port number: {} (must be 1-65535)\n".format(p))
                        return
                except Exception:
                    print("\nInvalid port number: {}\n".format(p))
                    return

        if description:
            description = description.strip('"').strip("'").strip()

        # derive action by mode
        mode = state["mode"]
        action = "allow" if mode == "whitelist" else "deny"

        staged = self._stage_rule(action, source, ports, description)
        if staged:
            if mode == "whitelist":
                print('Staged (ALLOW/whitelist): {} {} ({})\n'.format(source, " ".join(ports), description or ""))
            else:
                print('Staged (DENY/blacklist): {} {} ({})\n'.format(source, " ".join(ports), description or ""))
        else:
            print("ACL rule already staged.\n")

    def unset_ntp_callback(self, key, param):
        if not param or param[0].endswith('?') or len(param) < 1:
            print('\n<NTP server> \t Specify NTP server name or IP address\n')
            return
        if "--force" in param:
            print("--force is not supported; only CLI-managed NTP peers may be removed")
            return 1
        target = self._normalize_ntp_target(" ".join(param))
        if not self._is_valid_ntp_target(target):
            print("Invalid NTP hostname: Please enter the correct hostname")
            return 1
        if self._ntpsec_operation("unset", [target]):
            print("Successfully unset ntp {}\n".format(" ".join(param)))
            return 0
        return 1


    def unset_acl_callback(self, key, param):
        """
        NEW:
          unset acl <IP/network> <port|icmp|ping> [...] | all

        Removes from BOTH:
          - staging
          - live AELLA_INPUT_CHAIN (only AELLA-managed user rules)
        """
        if not param or len(param) < 2:
            print("\n<IP/network> <port|icmp|ping> [...] | all  Remove ACL rule")
            print("Examples:")
            print("  unset acl 192.168.1.100 22")
            print("  unset acl 192.168.1.0/24 80 443")
            print("  unset acl 10.0.0.0/8 all\n")
            return

        state = self._load_acl_state()
        if not state:
            print("\nACL policy is not initialized. Run 'set acl policy' first.\n")
            return

        source = param[0]
        if "/" in source:
            parts = source.split("/")
            if not self.valid_ipv4_address(parts[0]) or not parts[1].isdigit() or int(parts[1]) > 32:
                print("\nInvalid network format: Use CIDR notation (e.g., 192.168.1.0/24)\n")
                return
        else:
            if not self.valid_ipv4_address(source):
                print("\nInvalid IP address format: {}\n".format(source))
                return

        ports = param[1:]
        if "all" in ports:
            if len(ports) > 1:
                print('\nCannot specify "all" with other ports\n')
                return
            ports = ["all"]
        else:
            # validate port numbers
            for p in ports:
                if p in ("icmp", "ping"):
                    continue
                if not p.isdigit():
                    print("\nInvalid port: {}\n".format(p))
                    return
                n = int(p)
                if n < 1 or n > 65535:
                    print("\nInvalid port number: {} (must be 1-65535)\n".format(p))
                    return

            normalized_ports = []
            for p in ports:
                p = "icmp" if p == "ping" else p
                if p not in normalized_ports:
                    normalized_ports.append(p)
            ports = normalized_ports

        # 1) remove from staging
        data = self._load_acl_staging()
        rules = data.get("rules", [])
        before = len(rules)
        # match by source+ports regardless of action/desc
        new_rules = [r for r in rules if not (r.get("source") == source and r.get("ports") == ports)]
        data["rules"] = new_rules
        self._save_acl_staging(data)
        staged_removed = before - len(new_rules)

        # 2) remove from live chain (only AELLA user rules)
        live_removed = 0
        iface = state["iface"]
        iface_ip = None
        try:
            iface_ip = self._get_iface_ipv4(iface)
        except Exception:
            iface_ip = None

        if iface_ip and self._iptables_chain_exists(AELLA_INPUT_CHAIN):
            # delete rules by reconstructing rule args; try both -s omitted and -s 0.0.0.0/0 when any
            mode = state["mode"]
            action = "allow" if mode == "whitelist" else "deny"

            for p in ports:
                desc_candidates = [""]  # we don't know desc; we will delete by scanning and matching -s/-d/--dport/-j and prefix.
                # Safer approach: scan -S chain and delete matching lines
                rc, out, _ = self._run_cmd(f"sudo iptables -S {AELLA_INPUT_CHAIN}")
                if rc == 0 and out:
                    for line in out.splitlines():
                        if not line.startswith(f"-A {AELLA_INPUT_CHAIN}"):
                            continue
                        if ACL_COMMENT_PREFIX.strip() not in line:
                            continue
                        if "-d {}/32".format(iface_ip) not in line:
                            continue
                        # port match
                        if p == "all":
                            if "--dport" in line:
                                continue
                        else:
                            if p in ("icmp", "ping"):
                                if "-p icmp" not in line:
                                    continue
                                if "--icmp-type" in line and "--icmp-type 8" not in line and "--icmp-type echo-request" not in line:
                                    continue
                            elif f"--dport {p}" not in line:
                                continue
                        # target match
                        want_target = "ACCEPT" if action == "allow" else "DROP"
                        if f"-j {want_target}" not in line:
                            continue
                        # source match (any-source equivalence)
                        if source in ("0.0.0.0/0", "0.0.0.0"):
                            # accept both: with -s 0.0.0.0/0 OR no -s
                            pass
                        else:
                            if f"-s {source}" not in line:
                                continue

                        del_line = line.replace(f"-A {AELLA_INPUT_CHAIN}", f"-D {AELLA_INPUT_CHAIN}", 1)
                        self._run_cmd("sudo iptables " + del_line)
                        live_removed += 1

        if staged_removed or live_removed:
            if live_removed > 0:
                self._persist_iptables_rules()
            print(f"\nRemoved {live_removed} live rule(s), removed {staged_removed} staged rule(s).\n")
        else:
            print("\nNo matching ACL rules found to remove.\n")
            print('Use "show acl" to see current rules.\n')

    def unset_interface_callback(self, key, param):
        if param and param[0].rstrip("?") == "mgt":
            if len(param) < 2 or param[0].endswith("?"):
                print("\nip         Unset management IP address and netmask")
                print("gateway    Unset management default gateway")
                print("restart    Restart management interface\n")
                return
            option = param[1]
            if option == "ip":
                changed = self._apply_mgt_transaction(remove_address=True, remove_netmask=True)
            elif option == "gateway":
                changed = self._apply_mgt_transaction(remove_gateway=True)
            elif option == "restart":
                self._apply_mgt_transaction(restart=True)
                return
            else:
                print('Invalid option: Available options are "ip", "gateway" and "restart"')
                return
            if changed and self._mgt_last_changed:
                print("Run 'unset interface mgt restart' command to apply the changes.\n")
            return
        if self.is_sensor_host_mode():
            self.unset_interface_sensor(param)
            return
        if not param or len(param) < 2:
            print("\n<Interface Name>  Specify a supported interface (data1g or data10g)\n")
            return
        interface = param[0]
        option = param[1]
        if not re.fullmatch(r"data1(?:0)?g", interface) or not self.is_device_exist(interface):
            print("\n<Interface Name>  Specify a supported interface (data1g or data10g)\n")
            return
        if option == "ip":
            contents = ["auto {}".format(interface), "iface {} inet manual".format(interface)]
            if not self.update_interface_file(interface, contents):
                return
            print("Run 'unset interface {} restart' command to apply the changes.\n".format(interface))
        elif option == "gateway":
            route_proc = subprocess.run(
                ["ip", "route", "show", "table", "2"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            default_line = next((line for line in route_proc.stdout.splitlines() if line.startswith("default ")), None)
            if not default_line:
                print("Could not find the default gateway on the interface {}\n".format(interface))
                return
            match = re.match(
                r"^default\s+via\s+(\d+\.\d+\.\d+\.\d+)\s+dev\s+([A-Za-z0-9_.:-]{1,15})(?:\s|$)",
                default_line,
            )
            if not match or match.group(2) != interface:
                print("Could not delete the default gateway due to interface mismatch\n")
                return
            delete_proc = subprocess.run(
                ["ip", "route", "del", "default", "via", match.group(1),
                 "dev", match.group(2), "table", "2"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if delete_proc.returncode != 0:
                print("Could not delete the default gateway: {}".format(
                    delete_proc.stderr.strip() or delete_proc.stdout.strip()
                ))
                return
            print("Successfully deleted the default gateway: {}\n".format(default_line))
        elif option == "restart":
            print("Restarting network interface. You need to use new IP address to reconnect...\n")
            self._restart_interface_with_verification(interface)
        else:
            print('Invalid option: Available options are "ip", "gateway", and "restart"')

    def complete_unset(self, text, line, begidx, endidx):
        if not text:
            completions = self.unset_command_help.keys()
        elif line.startswith('unset interface'):
            return self.complete_unset_interface(text, line, begidx, endidx)
        else:
            completions = [f for f in self.unset_command_help.keys() if f.startswith(text)]
        return completions

    # Unset command
    @log_cmd
    def do_unset(self, line):
        """ Unset command """
        return self._on_nested_command(line, self.unset_command_help, self.unset_command_callback)

    def show_version(self, key, param):
        print("")
        print("Appliance Version : 3.10.1-appliance")
        print("Hardware Revision : 1.5\n")
        for path, label in (
            ("/sys/class/dmi/id/product_name", "Product Name"),
            ("/sys/class/dmi/id/product_serial", "Serial Number"),
        ):
            try:
                value = Path(path).read_text(encoding="utf-8", errors="replace").strip()
                print("{:<15}: {}".format(label, value))
            except OSError:
                print("{:<15}: unavailable".format(label))
        print("\nAppliance CPUs")
        print("------------------------------")
        cpu_info = subprocess.run(
            ["lscpu"], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, check=False,
        )
        if cpu_info.returncode == 0:
            for line in cpu_info.stdout.splitlines():
                if re.match(r"^(Thread|Core|Socket|CPU\()", line):
                    print(line)
        print("\nAppliance Memory")
        print("--------------------------------")
        try:
            for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
                if line.startswith(("Mem", "Swap")):
                    print(line)
        except OSError as exc:
            print("Unable to read memory information: {}".format(exc))
        print("")

    def show_hostname(self, key, param):
        self.shell_cmd_exec('hostname')

    def is_valid_hostname(self, hostname):
        if not hostname:
            return False
        if hostname[-1] == ".":
            hostname = hostname[:-1]
        if not hostname:
            return False
        allowed = re.compile("(?!-)[A-Z\d-]{1,63}(?<!-)$", re.IGNORECASE)
        return all(allowed.match(x) for x in hostname.split("."))

    def set_hostname_callback(self, key, param):
        if not param or len(param) != 1 or param[0].endswith("?"):
            print("\n<String> \t Specify hostname string\n")
            return
        hostname = param[0]
        if len(hostname) > 64 or not self.is_valid_hostname(hostname):
            print("\nError: Invalid hostname format.\n")
            return

        hosts_path = Path("/etc/hosts")
        try:
            current = subprocess.run(
                ["hostname"], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            ).stdout.strip()
            original = hosts_path.read_text(encoding="utf-8")
            updated_lines = []
            for line in original.splitlines(keepends=True):
                body, marker, comment = line.partition("#")
                if current:
                    body = re.sub(
                        r"(?<![A-Za-z0-9_.-]){}(?![A-Za-z0-9_.-])".format(re.escape(current)),
                        hostname,
                        body,
                    )
                updated_lines.append(body + marker + comment)
            original_stat = os.stat(hosts_path)
            _atomic_replace_text_file(str(hosts_path), "".join(updated_lines))
            os.chown(str(hosts_path), original_stat.st_uid, original_stat.st_gid)
            os.chmod(str(hosts_path), stat.S_IMODE(original_stat.st_mode))

            result = subprocess.run(
                ["hostnamectl", "set-hostname", hostname],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if result.returncode != 0:
                _atomic_replace_text_file(str(hosts_path), original)
                os.chown(str(hosts_path), original_stat.st_uid, original_stat.st_gid)
                os.chmod(str(hosts_path), stat.S_IMODE(original_stat.st_mode))
                print("Failed to set hostname: {}".format(result.stderr.strip() or result.stdout.strip()))
                return
            print("Successfully set hostname")
        except Exception as exc:
            print("Failed to set hostname: {}".format(exc))

    @staticmethod
    def update_patch_history(patch_name, patch_history, log_file, success, msg):
        timestamp = str(datetime.datetime.now())
        state = "Success" if success else "Fail"
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._+-]{0,127}", patch_name) or ".." in patch_name:
            raise ValueError("Invalid patch name")
        expected_log = Path(PATCH_LOG_DIR) / "{}.log".format(patch_name)
        if Path(log_file) != expected_log:
            raise ValueError("Patch log path is outside the protected patch directory")
        patch_history[patch_name] = {"timestamp": timestamp, "state": state}
        _ensure_patch_storage()
        _write_root_text_file(
            PATCH_HISTORY,
            json.dumps(patch_history, sort_keys=True, indent=4, ensure_ascii=False),
        )
        log_content = "Patch starts at {}\n{}\nPatch result: {}".format(timestamp, msg, state)
        _write_root_text_file(log_file, log_content)

    def set_patches_callback(self, key, param):
        """Apply only operator-approved Stellar hotfix packages."""
        if not param or param[0].endswith("?"):
            print('\nUse: set patches apply <approved_patch_name>\n')
            return
        if param[0] != "apply":
            print("Direct OS package installation is disabled in the restricted Appliance CLI.")
            print("Use 'set patches apply <approved_patch_name>' for an operator-approved Stellar hotfix.")
            return
        if len(param) != 2:
            print('\nUse: set patches apply <approved_patch_name>\n')
            return

        patch_name = param[1]
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._+-]{0,127}", patch_name) or ".." in patch_name:
            print("Invalid patch name. Directory components and special characters are not allowed.")
            return

        try:
            _ensure_patch_storage()
            log_file = os.path.join(PATCH_LOG_DIR, "{}.log".format(patch_name))
            local_file = os.path.join(PATCH_DIR, patch_name)
            try:
                patch_history = json.loads(_read_root_text_file(PATCH_HISTORY))
                if not isinstance(patch_history, dict):
                    patch_history = {}
            except Exception:
                patch_history = {}

            # Remove any pre-existing file/link before wget creates the target.
            if os.path.lexists(local_file):
                local_stat = os.lstat(local_file)
                if stat.S_ISDIR(local_stat.st_mode):
                    print("Refusing unsafe patch target path.")
                    return
                os.unlink(local_file)

            url = "https://192.168.122.2:8443/hotfix/{}".format(patch_name)
            download_cmd = [
                "wget", "--user={}".format(META_USER),
                "--password={}".format(META_TOKEN), "-O",
                local_file, "--no-check-certificate", url,
            ]
            downloaded, output = self.run_command_with_stderr(download_cmd)
            if not downloaded:
                message = output.decode("utf-8", errors="replace").strip() if isinstance(output, bytes) else str(output)
                error_msg = "Failed to download patch: {}".format(message)
                print(error_msg)
                self.update_patch_history(patch_name, patch_history, log_file, False, error_msg)
                return

            success, output = self.run_command_with_stderr(["dpkg", "-i", local_file])
            message = "Success" if success else (
                output.decode("utf-8", errors="replace").strip() if isinstance(output, bytes) else str(output)
            )
            self.update_patch_history(patch_name, patch_history, log_file, success, message)
            print(message)
        except Exception as exc:
            print("Failed to apply Stellar hotfix: {}".format(exc))

    def set_autostart_callback(self, key, param):
        """Configure VM auto start."""
        if not param or len(param) > 2:
            print("\n<VM Name> [enable|disable]  Specify VM name and enable/disable auto start\n")
            return
        vm_name = param[0].rstrip("?")
        if param[0].endswith("?") or not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm_name):
            print("Invalid VM name.")
            return
        vm_list = self.get_vm_list()
        if vm_name not in vm_list:
            print('VM "{}" not found. Available VMs: {}'.format(vm_name, ", ".join(vm_list) if vm_list else "none"))
            return

        enable = None
        if len(param) == 2:
            option = param[1].lower().rstrip("?")
            if option == "enable":
                enable = True
            elif option == "disable":
                enable = False
            else:
                print('Invalid option: Available options are "enable" and "disable"')
                return

        try:
            if enable is None:
                info = subprocess.run(
                    ["virsh", "dominfo", vm_name],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    text=True, check=False,
                )
                parsed = self._parse_virsh_autostart(info.stdout) if info.returncode == 0 else None
                enable = parsed is not True

            command = ["virsh", "autostart"]
            if not enable:
                command.append("--disable")
            command.append(vm_name)
            result = subprocess.run(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if result.returncode != 0:
                print("Failed to configure auto start for VM '{}': {}\n".format(
                    vm_name, result.stderr.strip() or result.stdout.strip() or "Unknown error"
                ))
                return

            check = subprocess.run(
                ["virsh", "dominfo", vm_name],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            parsed = self._parse_virsh_autostart(check.stdout) if check.returncode == 0 else None
            status = "enabled" if parsed is True else "disabled" if parsed is False else "unknown"
            print("VM '{}' auto start status: {}\n".format(vm_name, status))
        except Exception as exc:
            print("Failed to configure auto start for VM '{}': {}\n".format(vm_name, exc))

    # clear commands
    def clear_cli_callback(self, key, param):
        if not param or param[0].rstrip("?") != "history" or len(param) != 1 or param[0].endswith("?"):
            print("\nhistory    Clear CLI history\n")
            return
        try:
            log_dir = Path(LOG_DIR)
            if os.geteuid() == 0:
                gid = _ensure_root_owned_directory(str(log_dir), mode=0o750)
            else:
                gid = os.getgid()
            log_path = log_dir / "aella_cli.log"
            backup_stamp = datetime.datetime.now().strftime("%Y-%m-%d_%H%M%S")
            backup_path = log_dir / ("aella_cli.log_" + backup_stamp)

            if os.path.lexists(log_path):
                log_stat = os.lstat(log_path)
                if stat.S_ISREG(log_stat.st_mode) and log_stat.st_nlink == 1:
                    if os.path.lexists(backup_path):
                        os.unlink(backup_path)
                    shutil.copyfile(log_path, backup_path)
                    if os.geteuid() == 0:
                        os.chown(backup_path, 0, gid)
                        os.chmod(backup_path, 0o640)
                else:
                    os.unlink(log_path)

            timestamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            log_content = "{},000|INFO|0|log|Run command: ### clear cli history ###\n".format(timestamp)
            _atomic_replace_text_file(str(log_path), log_content)
            if os.geteuid() == 0:
                os.chown(log_path, 0, gid)
                os.chmod(log_path, 0o640)

            backups = []
            for entry in log_dir.glob("aella_cli.log_*"):
                if not re.fullmatch(r"aella_cli\.log_\d{4}-\d{2}-\d{2}_\d{6}", entry.name):
                    continue
                entry_stat = os.lstat(entry)
                if stat.S_ISREG(entry_stat.st_mode) and entry_stat.st_nlink == 1:
                    backups.append(entry)
            backups.sort(key=lambda path: path.name, reverse=True)
            for old_backup in backups[5:]:
                old_backup.unlink()
        except Exception as exc:
            print("Failed to clear CLI history: {}".format(exc))

    def monitor_vm_callback(self, key, param):
        """Monitor VM resource usage without invoking a shell."""
        if param and len(param) == 1 and param[0] in {"?", "help"}:
            print("\nhtop <VM Name>  Monitor a specific VM with htop")
            print("                List running VMs with resource usage\n")
            return

        if param and param[0] == "htop":
            if len(param) != 2 or not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", param[1]):
                print("\n<VM Name>  Specify a valid VM name\n")
                return
            vm_name = param[1]
            if vm_name not in self.get_vm_list():
                print('VM "{}" not found.\n'.format(vm_name))
                return
            pid_file = Path("/run/libvirt/qemu") / "{}.pid".format(vm_name)
            try:
                pid_text = _read_root_text_file(pid_file).strip()
                if not re.fullmatch(r"[1-9][0-9]{0,9}", pid_text):
                    raise ValueError("Invalid VM PID file")
                htop = shutil.which("htop", path="/usr/bin:/usr/sbin:/bin:/sbin")
                if not htop:
                    print("htop is not installed.\n")
                    return
                username = _get_invoking_username()
                if not username:
                    print("Unable to resolve the invoking account; monitor command denied.\n")
                    return
                argv = [htop, "-p", pid_text]
                if username != "root":
                    argv = ["/usr/bin/sudo", "-u", username, "--"] + argv
                subprocess.call(argv, shell=False)
            except Exception as exc:
                print('Failed to launch htop for VM "{}": {}\n'.format(vm_name, exc))
            return

        try:
            vm_result = subprocess.run(
                ["virsh", "list", "--name"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if vm_result.returncode != 0:
                print("Failed to get VM list\n")
                return
            vm_list = [name.strip() for name in vm_result.stdout.splitlines() if name.strip()]
            if not vm_list:
                print("No running VMs found\n")
                return

            total_cores = os.cpu_count() or 1
            mem_total_kb = 0
            try:
                for line in Path("/proc/meminfo").read_text(encoding="utf-8").splitlines():
                    if line.startswith("MemTotal:"):
                        mem_total_kb = int(line.split()[1])
                        break
            except (OSError, ValueError, IndexError):
                pass

            print("\n" + "=" * 140)
            print("VM Resource Usage Monitor")
            print("=" * 140)
            print("{:<15} {:<8} {:<12} {:<12} {:<12} {:<10} {:<12} {:<12} {:<12} {:<8} {:<8}".format(
                "VM", "PID", "CPU(ps%)", "CPU(host%)", "CPU(vcpu%)", "RSS(GB)",
                "Mem(host%)", "Mem(alloc%)", "Alloc(GB)", "vCPU", "Status"
            ))
            print("-" * 140)

            for vm in vm_list:
                if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", vm):
                    continue
                pid_file = Path("/run/libvirt/qemu") / "{}.pid".format(vm)
                try:
                    pid = _read_root_text_file(pid_file).strip()
                    if not re.fullmatch(r"[1-9][0-9]{0,9}", pid):
                        continue
                    ps_result = subprocess.run(
                        ["ps", "-p", pid, "-o", "%cpu,rss,nlwp", "--no-headers"],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, check=False,
                    )
                    ps_fields = ps_result.stdout.strip().split()
                    if ps_result.returncode != 0 or len(ps_fields) < 3:
                        continue
                    cpu_percent = float(ps_fields[0])
                    rss_kb = int(ps_fields[1])
                    threads = int(ps_fields[2])
                    if rss_kb <= 0:
                        continue

                    dominfo = subprocess.run(
                        ["virsh", "dominfo", vm],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, check=False,
                    ).stdout
                    memory_match = re.search(r"^\s*Memory:\s*(\d+)", dominfo, re.MULTILINE)
                    max_memory_match = re.search(r"^\s*Max memory:\s*(\d+)", dominfo, re.MULTILINE)
                    cpu_match = re.search(r"^\s*CPU\(s\):\s*(\d+)", dominfo, re.MULTILINE)
                    allocated_mem_kb = int(memory_match.group(1)) if memory_match else (
                        int(max_memory_match.group(1)) if max_memory_match else 0
                    )
                    vcpus = int(cpu_match.group(1)) if cpu_match else threads

                    rss_mb = rss_kb / 1024.0
                    rss_gb = rss_kb / 1024.0 / 1024.0
                    allocated_mem_mb = allocated_mem_kb / 1024.0 if allocated_mem_kb else 0
                    cpu_host_percent = cpu_percent / total_cores if total_cores else 0
                    cpu_vcpu_percent = cpu_percent / vcpus if vcpus else 0
                    mem_host_percent = (rss_kb / mem_total_kb) * 100 if mem_total_kb else 0
                    mem_alloc_percent = (rss_mb / allocated_mem_mb) * 100 if allocated_mem_mb else 0
                    alloc_gb = allocated_mem_mb / 1024.0 if allocated_mem_mb else 0

                    status = "CRIT" if cpu_host_percent > 80 or mem_host_percent > 90 else (
                        "WARN" if cpu_host_percent > 50 or mem_host_percent > 75 else "OK"
                    )
                    print("{:<15} {:<8} {:<12} {:<12} {:<12} {:<10} {:<12} {:<12} {:<12} {:<8} {:<8}".format(
                        vm, pid, "{:.1f}".format(cpu_percent), "{:.1f}".format(cpu_host_percent),
                        "{:.1f}".format(cpu_vcpu_percent), "{:.2f}".format(rss_gb),
                        "{:.1f}".format(mem_host_percent),
                        "{:.1f}".format(mem_alloc_percent) if allocated_mem_mb else "N/A",
                        "{:.2f}".format(alloc_gb) if allocated_mem_mb else "N/A",
                        vcpus, status,
                    ))
                except (OSError, ValueError, IndexError):
                    continue

            print("-" * 140)
            print("Legend:")
            print("  CPU(host%): >50 WARN, >80 CRIT (CPU(ps%) / {} cores)".format(total_cores))
            print("  Mem(host%): >75 WARN, >90 CRIT (RSS / host MemTotal)")
            print("  CPU(vcpu%) / Mem(alloc%): Reference metrics only")
            print('  Use "monitor vm htop <VM Name>" for detailed process monitoring\n')
        except Exception as exc:
            print("Failed to monitor VMs: {}\n".format(exc))

    def monitor_system_callback(self, key, param):
        """Check system health status using direct file reads and argv-only commands."""
        try:
            try:
                loadavg = Path("/proc/loadavg").read_text(encoding="utf-8").strip().split()
                load_1min, load_5min, load_15min = map(float, loadavg[:3])
                cpu_cores = os.cpu_count() or 1
                per_core_1min = load_1min / cpu_cores
                per_core_5min = load_5min / cpu_cores
                per_core_15min = load_15min / cpu_cores
                status = "CRIT" if per_core_1min > 1.0 else "WARN" if per_core_1min > 0.7 else "OK"
                print("[{}]   load: {:.1f} {:.1f} {:.1f} (cores={}, per-core={:.2f} {:.2f} {:.2f})".format(
                    status, load_1min, load_5min, load_15min, cpu_cores,
                    per_core_1min, per_core_5min, per_core_15min,
                ))
            except Exception as exc:
                print("[ERR]  load: failed to check ({})".format(exc))

            try:
                meminfo = Path("/proc/meminfo").read_text(encoding="utf-8")
                values = {}
                for line in meminfo.splitlines():
                    fields = line.split()
                    if len(fields) >= 2 and fields[0].rstrip(":") in {"MemTotal", "MemAvailable", "SwapTotal", "SwapFree"}:
                        values[fields[0].rstrip(":")] = int(fields[1])
                mem_total = values.get("MemTotal", 0)
                mem_available = values.get("MemAvailable", 0)
                if mem_total > 0:
                    mem_percent = (mem_available / mem_total) * 100
                    total_gb = mem_total / (1024.0 * 1024.0)
                    available_gb = mem_available / (1024.0 * 1024.0)
                    status = "OK" if mem_percent > 20 else "WARN"
                    print("[{}]   mem: {:.0f}% available ({:.0f}GiB / {:.0f}GiB)".format(
                        status, mem_percent, available_gb, total_gb,
                    ))
                else:
                    print("[ERR]  mem: failed to get memory info")
                swap_total = values.get("SwapTotal", 0)
                swap_free = values.get("SwapFree", 0)
                if swap_total > 0:
                    swap_used_gb = (swap_total - swap_free) / (1024.0 * 1024.0)
                    print("[WARN] swap: {:.1f}G used".format(swap_used_gb) if swap_free < swap_total else "[OK]   swap: not in use")
                else:
                    print("[OK]   swap: not configured")
            except Exception as exc:
                print("[ERR]  mem/swap: failed to check ({})".format(exc))

            def report_filesystem(mountpoint, label):
                proc = subprocess.run(
                    ["df", "-h", mountpoint],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                    text=True, check=False,
                )
                rows = proc.stdout.splitlines()
                if proc.returncode != 0 or len(rows) < 2:
                    return
                parts = rows[-1].split()
                if len(parts) < 5:
                    return
                try:
                    usage = int(parts[4].rstrip("%"))
                except ValueError:
                    return
                status = "OK" if usage < 80 else "WARN"
                print("[{}]   {}: {}% used ({} / {})".format(status, label, usage, parts[2], parts[1]))

            try:
                report_filesystem("/", "/")
            except Exception as exc:
                print("[ERR]  /: failed to check ({})".format(exc))
            if os.path.exists("/stellar"):
                try:
                    report_filesystem("/stellar", "/stellar")
                except Exception:
                    pass

            try:
                libvirt_status = ""
                for service in ("libvirtd", "virtqemud"):
                    proc = subprocess.run(
                        ["systemctl", "is-active", service],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, check=False,
                    )
                    if proc.returncode == 0 and proc.stdout.strip():
                        libvirt_status = proc.stdout.strip()
                        break
                if not libvirt_status:
                    print("[WARN] libvirt: service not found")
                else:
                    running = subprocess.run(
                        ["virsh", "list", "--name"],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, check=False,
                    )
                    defined = subprocess.run(
                        ["virsh", "list", "--all", "--name"],
                        stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                        text=True, check=False,
                    )
                    running_count = len([name for name in running.stdout.splitlines() if name.strip()]) if running.returncode == 0 else 0
                    defined_count = len([name for name in defined.stdout.splitlines() if name.strip()]) if defined.returncode == 0 else 0
                    if libvirt_status == "active":
                        if running_count or defined_count:
                            print("[OK]   libvirt: active (vms running {} / defined {})".format(running_count, defined_count))
                        else:
                            print("[OK]   libvirt: active")
                    else:
                        print("[WARN] libvirt: {}".format(libvirt_status))
            except Exception as exc:
                print("[ERR]  libvirt: failed to check ({})".format(exc))
        except Exception as exc:
            print("System health check failed: {}".format(exc))

    def show_patch_history_callback(key, params):
        try:
            _ensure_patch_storage()
            try:
                patch_history = json.loads(_read_root_text_file(PATCH_HISTORY))
                if not isinstance(patch_history, dict):
                    patch_history = {}
            except Exception:
                patch_history = {}

            patch = params[0] if params else ""
            if patch:
                if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._+-]{0,127}", patch) or ".." in patch:
                    print("Invalid patch name.")
                    return
                if patch not in patch_history:
                    print("There is no history associated with the specified patch")
                    return
                state = patch_history[patch].get("state", "Unknown")
                log_file = Path(PATCH_LOG_DIR) / "{}.log".format(patch)
                try:
                    patch_log = _read_root_text_file(log_file)
                except Exception:
                    print("There is no history associated with the specified patch")
                    return
                output = "Patch state: {}".format(state)
                output += "\n=====================\n"
                output += patch_log
            else:
                records = []
                for patch_name, patch_info in patch_history.items():
                    if not isinstance(patch_name, str) or not isinstance(patch_info, dict):
                        continue
                    records.extend([
                        "Patch name: {}".format(patch_name),
                        "State:      {}".format(patch_info.get("state", "Unknown")),
                        "Time:       {}".format(patch_info.get("timestamp", "Unknown")),
                        "====================",
                    ])
                output = "\n".join(records) if records else "No patch history"
            print(output)
        except Exception as exc:
            print("Failed to get patch history: {}".format(exc))

    def _should_debug():
        return os.environ.get("AELLA_CLI_DEBUG") == "1"

    def _debug_print(self, msg):
        if self._should_debug():
            print(msg)

    def write_full_interfaces_file(self, lines):
        main_path = NETWORK_INTERFACES_PATH
        try:
            _atomic_replace_text_file(
                main_path,
                "\n".join([line.rstrip("\n") for line in lines]) + "\n",
            )
            with open(main_path, 'r') as f:
                final = f.read()
            if not final.strip():
                print("Failed to update interface configuration: file is empty")
                return False
            if "iface lo inet loopback" not in final and "source /etc/network/interfaces.d/*" not in final:
                print("Failed to update interface configuration: missing base stanza/source")
                return False
            return True
        except Exception as e:
            print('Failed to update interface configuration')
            print(e)
            return False

    def update_interface_file(self, interface, contents):
        """Update interface configuration file block only.
        For DP appliances: mgt in /etc/network/interfaces, data1g/data10g in interfaces.d/
        For Sensor/KVM installers: mgt/host/hostmgmt in /etc/network/interfaces.d/*.cfg
        """
        if interface == "mgt":
            print("Management interface must use the canonical management editor")
            return False
        try:
            for line in contents:
                if re.match(r'^\s*source\s+/etc/network/interfaces\.d/\*', line):
                    print("Invalid interface block contents: contains source line")
                    return False
                if re.match(r'^\s*iface\s+lo\s+inet\s+loopback', line):
                    print("Invalid interface block contents: contains loopback stanza")
                    return False

            new_block = [line.rstrip("\n") for line in contents]
            cfg_path = self._find_iface_config_path(interface)
            main_path = "/etc/network/interfaces"

            if cfg_path and cfg_path != main_path:
                return self._write_iface_config_file_with_backup(cfg_path, new_block)

            if os.path.exists(main_path):
                with open(main_path, 'r') as f:
                    existing = f.read().splitlines()
            else:
                existing = []

            start = None
            end = None
            in_block = False
            for idx, line in enumerate(existing):
                if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(interface)), line):
                    if start is None:
                        start = idx
                        in_block = True
                elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                    end = idx
                    in_block = False
                    break
            if start is not None and end is None:
                end = len(existing)

            if start is None:
                if self._uses_interfaces_d_source() and interface in self._SENSOR_IFACE_CFG_HINTS:
                    target = self._default_iface_config_path(interface)
                    if target != main_path:
                        return self._write_iface_config_file_with_backup(target, new_block)
                updated = existing + ([""] if existing and existing[-1].strip() else []) + new_block
            else:
                updated = existing[:start] + new_block + existing[end:]

            return self._write_interfaces_file_with_backup(updated)
        except Exception as e:
            print('Failed to update interface configuration')
            print(e)
            return False

    # Update gateway in the routing table 1 (mgt) or table 2 (data) by calling
    # /etc/network/if-up.d/dp_mgt_data script
    def update_dp_mgt_data(self, data_intf_gw, interface):
        try:
            with open('/etc/network/if-up.d/dp_mgt_data', 'rt') as f:
                content = f.read()
            new_content = re.sub(r'DATA_GATEWAY=\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}.*', 'DATA_GATEWAY={0}'.format(data_intf_gw), content)
            with open('/etc/network/if-up.d/dp_mgt_data', 'wt') as f:
                f.write(new_content)
            return True
        except:
            print("Failed to update {0} interface gateway".format(interface))
            return False

    # Get the interface name out of a line from /etc/network/interfaces
    @staticmethod
    def get_interface_from_line(line):
        interface = ""
        tokens = re.match("\s*iface\s+(\S+)\s+inet\s+(\S+).*", line)
        if tokens:
            interface = tokens.group(1)
        else:
            auto_tokens = re.match("\s*auto\s+(\S+).*", line)
            if auto_tokens:
                interface = auto_tokens.group(1)
        return interface.strip()

    # Check interface existence
    @staticmethod
    def iface_exists(interface):
        if not isinstance(interface, str) or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface):
            return False
        try:
            proc = subprocess.run(
                ["ip", "link", "show", "dev", interface],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            return proc.returncode == 0
        except Exception:
            return False

    def cidr_to_netmask(cidr):
        address, net_bits = cidr.split('/')
        if net_bits is None or net_bits == "":
            netmask = "255.255.255.255"
        else:
            if re.match("(\d+\.\d+\.\d+\.\d+)", net_bits):
                netmask = net_bits
            else:
                host_bits = 32 - int(net_bits)
                netmask = socket.inet_ntoa(struct.pack('!I', (1 << 32) - (1 << host_bits)))
        if (not re.match("(\d+\.\d+\.\d+\.\d+)", netmask) or
                not re.match("(\d+\.\d+\.\d+\.\d+)", address)):
            address = ""
            netmask = ""
        return address, netmask

    def _parse_set_interface_args(self, tokens):
        parsed = {"ip": None, "gateway": None, "dns": [], "restart": False}
        i = 0
        while i < len(tokens):
            key = tokens[i].lower()
            if key == "restart":
                parsed["restart"] = True
                i += 1
                continue
            if key not in {"ip", "gateway", "dns"}:
                raise ValueError("Invalid option: {}".format(tokens[i]))
            if i + 1 >= len(tokens):
                raise ValueError("Missing value for {}".format(tokens[i]))
            if key == "ip":
                parsed["ip"] = tokens[i + 1]
                i += 2
            elif key == "gateway":
                parsed["gateway"] = tokens[i + 1]
                i += 2
            else:
                dns_list = []
                i += 1
                while i < len(tokens) and tokens[i].lower() not in {"ip", "gateway", "dns", "restart"}:
                    dns_list.append(tokens[i])
                    i += 1
                if not dns_list:
                    raise ValueError("Missing DNS server IP address")
                parsed["dns"] = dns_list
        return parsed

    @staticmethod
    def _read_text_exact(path):
        with open(path, "r", encoding="utf-8", newline="") as stream:
            return stream.read()

    @staticmethod
    def _mgt_static_stanza_bounds(text):
        lines = text.splitlines(keepends=True)
        starts = [
            index for index, line in enumerate(lines)
            if re.match(r"^\s*iface\s+mgt\s+inet\s+static(?:\s*(?:#.*)?)?(?:\r?\n)?$", line)
        ]
        if len(starts) != 1:
            raise ValueError(
                "Canonical management configuration must contain exactly one "
                "'iface mgt inet static' stanza"
            )
        start = starts[0]
        end = len(lines)
        for index in range(start + 1, len(lines)):
            if re.match(r"^\s*iface\s+\S+\s+", lines[index]):
                end = index
                break
        return lines, start, end

    def _render_mgt_ipv4_config(
        self,
        original,
        address=None,
        netmask=None,
        gateway=None,
        dns_nameservers=None,
        remove_address=False,
        remove_netmask=False,
        remove_gateway=False,
        remove_dns=False,
    ):
        lines, start, end = self._mgt_static_stanza_bounds(original)
        replacements = {
            "address": (address, remove_address),
            "netmask": (netmask, remove_netmask),
            "gateway": (gateway, remove_gateway),
            "dns-nameservers": (dns_nameservers, remove_dns),
        }
        if address is not None:
            try:
                ipaddress.IPv4Address(address)
            except Exception as exc:
                raise ValueError("Invalid management IPv4 address") from exc
        if netmask is not None:
            try:
                network = ipaddress.IPv4Network("0.0.0.0/{}".format(netmask))
                netmask = str(network.netmask)
                replacements["netmask"] = (netmask, remove_netmask)
            except Exception as exc:
                raise ValueError("Invalid management IPv4 netmask") from exc
        if gateway is not None:
            try:
                ipaddress.IPv4Address(gateway)
            except Exception as exc:
                raise ValueError("Invalid management gateway") from exc
        if dns_nameservers is not None:
            if isinstance(dns_nameservers, str):
                dns_nameservers = dns_nameservers.split()
            normalized_dns = []
            for dns in dns_nameservers:
                try:
                    normalized_dns.append(str(ipaddress.IPv4Address(dns)))
                except Exception as exc:
                    raise ValueError("Invalid management DNS server: {}".format(dns)) from exc
            replacements["dns-nameservers"] = (normalized_dns, remove_dns)

        directive_indexes = {name: [] for name in replacements}
        indent = None
        newline = "\r\n" if "\r\n" in original else "\n"
        for index in range(start + 1, end):
            match = re.match(r"^(\s*)(address|netmask|gateway|dns-nameservers)\s+", lines[index])
            if match:
                directive_indexes[match.group(2)].append(index)
                if indent is None:
                    indent = match.group(1)
        indent = indent if indent is not None else "    "

        output = list(lines)
        insertions = []
        for name, (value, remove) in replacements.items():
            indexes = directive_indexes[name]
            if remove:
                for index in indexes:
                    output[index] = ""
                continue
            if value is None:
                for index in indexes[1:]:
                    output[index] = ""
                continue
            rendered_value = " ".join(value) if name == "dns-nameservers" else str(value)
            if indexes:
                original_line = lines[indexes[0]]
                original_body = original_line.rstrip("\r\n")
                original_newline = original_line[len(original_body):]
                original_indent = re.match(r"^(\s*)", original_body).group(1)
                inline_comment = re.search(r"(\s+#.*)$", original_body)
                comment_suffix = inline_comment.group(1) if inline_comment else ""
                output[indexes[0]] = "{}{} {}{}{}".format(
                    original_indent,
                    name,
                    rendered_value,
                    comment_suffix,
                    original_newline,
                )
                for index in indexes[1:]:
                    output[index] = ""
            else:
                insertions.append(
                    "{}{} {}{}".format(indent, name, rendered_value, newline)
                )
        if insertions:
            output[end:end] = insertions
        return "".join(output)

    def _update_mgt_ipv4_config(
        self,
        ip_cidr=None,
        gateway=None,
        dns_servers=None,
        remove_ip=False,
        remove_gateway=False,
        remove_dns=False,
    ):
        changes = {
            "gateway": gateway,
            "dns_nameservers": dns_servers,
            "remove_address": remove_ip,
            "remove_netmask": remove_ip,
            "remove_gateway": remove_gateway,
            "remove_dns": remove_dns,
        }
        if ip_cidr is not None:
            try:
                value = ipaddress.IPv4Interface(ip_cidr)
            except Exception as exc:
                raise ValueError("Invalid management IP address: {}".format(ip_cidr)) from exc
            changes["address"] = str(value.ip)
            changes["netmask"] = str(value.network.netmask)
        return self._apply_mgt_transaction(**changes)

    @staticmethod
    def _remove_mgt_from_noncanonical_text(text):
        lines = text.splitlines(keepends=True)
        output = []
        changed = False
        index = 0
        while index < len(lines):
            line = lines[index]
            activation = re.match(
                r"^(\s*)(auto|allow-hotplug)(\s+)([^#\r\n]*?)(\s*(?:#.*)?)(\r?\n)?$",
                line,
            )
            if activation:
                tokens = activation.group(4).split()
                if "mgt" in tokens:
                    changed = True
                    tokens = [token for token in tokens if token != "mgt"]
                    if tokens:
                        output.append(
                            "{}{}{}{}{}{}".format(
                                activation.group(1), activation.group(2), activation.group(3),
                                " ".join(tokens), activation.group(5), activation.group(6) or "",
                            )
                        )
                    index += 1
                    continue
            if re.match(r"^\s*iface\s+mgt\s+inet\s+static(?:\s|$)", line):
                changed = True
                index += 1
                while index < len(lines) and not re.match(
                    r"^\s*(iface|auto|allow-hotplug|source|source-directory|mapping)\b",
                    lines[index],
                ):
                    index += 1
                continue
            output.append(line)
            index += 1
        return "".join(output), changed

    def _collect_mgt_transaction(self, **changes):
        if not os.path.isfile(MGT_CONFIG_PATH):
            raise ValueError("Management configuration not found: {}".format(MGT_CONFIG_PATH))
        originals = {MGT_CONFIG_PATH: self._read_text_exact(MGT_CONFIG_PATH)}
        updated = {
            MGT_CONFIG_PATH: self._render_mgt_ipv4_config(originals[MGT_CONFIG_PATH], **changes)
        }
        candidates = []
        if os.path.isfile(NETWORK_INTERFACES_PATH):
            candidates.append(NETWORK_INTERFACES_PATH)
        if os.path.isdir(NETWORK_INTERFACES_DIR):
            for name in sorted(os.listdir(NETWORK_INTERFACES_DIR)):
                path = os.path.join(NETWORK_INTERFACES_DIR, name)
                if name.endswith(".cfg") and path != MGT_CONFIG_PATH and os.path.isfile(path):
                    candidates.append(path)
        final_texts = {MGT_CONFIG_PATH: updated[MGT_CONFIG_PATH]}
        for path in candidates:
            original = self._read_text_exact(path)
            cleaned, changed = self._remove_mgt_from_noncanonical_text(original)
            final_texts[path] = cleaned
            if changed:
                originals[path] = original
                updated[path] = cleaned
        static_locations = []
        for path, text in final_texts.items():
            count = len(re.findall(
                r"(?m)^\s*iface\s+mgt\s+inet\s+static(?:\s*(?:#.*)?)?$",
                text,
            ))
            static_locations.extend([path] * count)
        if static_locations != [MGT_CONFIG_PATH]:
            raise ValueError(
                "Management configuration must contain exactly one canonical "
                "'iface mgt inet static' stanza"
            )
        return originals, updated

    @staticmethod
    def _restore_text_files(originals, paths):
        failed_paths = []
        for path in reversed(paths):
            try:
                _atomic_replace_text_file(path, originals[path])
            except Exception:
                failed_paths.append(path)
        return list(reversed(failed_paths))

    def _apply_mgt_transaction(self, restart=False, **changes):
        self._mgt_last_changed = False
        try:
            originals, updated = self._collect_mgt_transaction(**changes)
        except Exception as exc:
            if str(exc).startswith("Management configuration not found:"):
                print(str(exc))
            else:
                print("Failed to update management configuration: {}".format(exc))
            return False
        write_order = [path for path in updated if path != MGT_CONFIG_PATH]
        write_order.append(MGT_CONFIG_PATH)
        changed_paths = [path for path in write_order if updated[path] != originals[path]]
        self._mgt_last_changed = bool(changed_paths)
        prepared = {}
        written = []
        try:
            for path in changed_paths:
                prepared[path] = _prepare_atomic_text_file(path, updated[path])
        except Exception as exc:
            for temporary_path in prepared.values():
                try:
                    os.unlink(temporary_path)
                except FileNotFoundError:
                    pass
            self._mgt_last_changed = False
            print("Failed to prepare management configuration: {}".format(exc))
            return False
        try:
            for path in changed_paths:
                try:
                    _commit_prepared_text_file(path, prepared[path])
                except _AtomicCommitError as exc:
                    if exc.replaced:
                        written.append(path)
                    raise
                written.append(path)
        except Exception as exc:
            failed_restore_paths = self._restore_text_files(originals, written)
            self._mgt_last_changed = False
            print("Failed to update management configuration: {}".format(exc))
            if failed_restore_paths:
                print(
                    "CRITICAL: Failed to restore management configuration: {}".format(
                        ", ".join(map(os.fspath, failed_restore_paths))
                    )
                )
            return False
        finally:
            for temporary_path in prepared.values():
                try:
                    os.unlink(temporary_path)
                except FileNotFoundError:
                    pass
        if restart and not self._restart_mgt_interface():
            failed_restore_paths = self._restore_text_files(originals, written)
            self._mgt_last_changed = False
            if failed_restore_paths:
                print(
                    "CRITICAL: Failed to restore management configuration: {}".format(
                        ", ".join(map(os.fspath, failed_restore_paths))
                    )
                )
            elif not self._restart_mgt_interface():
                print(
                    "CRITICAL: The previous management configuration was restored "
                    "on disk but could not be re-applied to the live interface. "
                    "Manual network recovery is required."
                )
            return False
        return True

    def _restart_mgt_interface(self):
        try:
            canonical = self._read_text_exact(MGT_CONFIG_PATH)
            lines, start, end = self._mgt_static_stanza_bounds(canonical)
            address = None
            netmask = None
            gateway = None
            for line in lines[start + 1:end]:
                match = re.match(r"^\s*(address|netmask|gateway)\s+(\S+)", line)
                if not match:
                    continue
                if match.group(1) == "address":
                    address = match.group(2)
                elif match.group(1) == "netmask":
                    netmask = match.group(2)
                else:
                    gateway = match.group(2)
            expected_ip = None
            if address and netmask:
                prefix = ipaddress.IPv4Network("0.0.0.0/{}".format(netmask)).prefixlen
                expected_ip = str(ipaddress.IPv4Interface("{}/{}".format(address, prefix)))
            elif address:
                raise ValueError("Management address requires a netmask")
        except Exception as exc:
            print("Failed to read management configuration: {}".format(exc))
            return False

        def read_runtime_addresses():
            proc = subprocess.run(
                ["ip", "-4", "-o", "addr", "show", "dev", "mgt", "scope", "global"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if proc.returncode != 0:
                error = (proc.stderr or "").strip()
                message = "Failed to read management IPv4 addresses"
                if error:
                    message += ": {}".format(error)
                print(message)
                return None

            addresses = []
            for match in re.finditer(r"\binet\s+(\S+)", proc.stdout or ""):
                try:
                    normalized = str(ipaddress.IPv4Interface(match.group(1)))
                except Exception:
                    print(
                        "Failed to parse management IPv4 address: {}".format(
                            match.group(1)
                        )
                    )
                    return None
                addresses.append(normalized)
            return addresses

        def read_runtime_routes():
            proc = subprocess.run(
                ["ip", "-4", "route", "show", "table", "main", "default"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if proc.returncode != 0:
                error = (proc.stderr or "").strip()
                message = "Failed to read main routing table"
                if error:
                    message += ": {}".format(error)
                print(message)
                return None
            return proc.stdout or ""

        def verify_expected_route(runtime_routes):
            expected_gateway_missing = gateway and not re.search(
                r"(?m)^\s*default\s+via\s+{}\s+dev\s+mgt(?:\s|$)".format(
                    re.escape(gateway)
                ),
                runtime_routes,
            )
            unexpected_gateway = not gateway and re.search(
                r"(?m)^\s*default(?:\s+via\s+\S+)?\s+dev\s+mgt(?:\s|$)",
                runtime_routes,
            )
            return not expected_gateway_missing and not unexpected_gateway

        commands = [
            ["ifup", "--no-act", "mgt"],
            ["sudo", "ifdown", "--force", "mgt"],
            ["sudo", "ifup", "mgt"],
        ]
        for command in commands:
            proc = subprocess.run(
                command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if proc.returncode != 0:
                error = (proc.stderr or "").strip()
                message = "Failed to restart management interface: {}".format(
                    " ".join(command)
                )
                if error:
                    message += ": {}".format(error)
                print(message)
                return False

        # The configuration file has already been replaced at this point.  An
        # ifdown based on the new file can therefore leave the old runtime IP on
        # the interface.  Before deleting anything, first make sure the new IP
        # and its route are live so an invalid new configuration does not remove
        # the only working management address.
        runtime_addresses = read_runtime_addresses()
        if runtime_addresses is None:
            return False
        if expected_ip and expected_ip not in runtime_addresses:
            print(
                "Failed to verify new management IPv4 address: expected {}, found {}".format(
                    expected_ip,
                    ", ".join(runtime_addresses) if runtime_addresses else "none",
                )
            )
            return False

        runtime_routes = read_runtime_routes()
        if runtime_routes is None or not verify_expected_route(runtime_routes):
            print("Failed to verify main routing table")
            return False

        # Converge the live interface to the canonical configuration.  Keep the
        # expected address and remove every stale global IPv4 address left by
        # the previous configuration.  For an explicit unset, remove them all.
        stale_addresses = [
            item for item in runtime_addresses if expected_ip is None or item != expected_ip
        ]
        for stale_address in stale_addresses:
            proc = subprocess.run(
                ["sudo", "ip", "-4", "addr", "del", stale_address, "dev", "mgt"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if proc.returncode != 0:
                # The address may have disappeared asynchronously.  Re-read it
                # before treating the deletion as a failure.
                current_addresses = read_runtime_addresses()
                if current_addresses is None or stale_address in current_addresses:
                    error = (proc.stderr or "").strip()
                    message = "Failed to remove stale management IPv4 address {}".format(
                        stale_address
                    )
                    if error:
                        message += ": {}".format(error)
                    print(message)
                    return False

        final_addresses = read_runtime_addresses()
        if final_addresses is None:
            return False
        expected_addresses = [expected_ip] if expected_ip else []
        if sorted(final_addresses) != sorted(expected_addresses):
            print(
                "Failed to converge management IPv4 addresses: expected {}, found {}".format(
                    ", ".join(expected_addresses) if expected_addresses else "none",
                    ", ".join(final_addresses) if final_addresses else "none",
                )
            )
            return False

        # Re-check the route after stale addresses have been removed.  The CLI
        # reports success only when both the persistent file and live state are
        # consistent with the requested management configuration.
        runtime_routes = read_runtime_routes()
        if runtime_routes is None or not verify_expected_route(runtime_routes):
            print("Failed to verify main routing table")
            return False
        return True

    def _set_mgt_interface(self, param):
        if len(param) < 2:
            print("Management interface option is required")
            return False
        if param[1] == "restart":
            if self._apply_mgt_transaction(restart=True):
                print("Management interface restarted successfully.")
                return True
            return False
        try:
            parsed = self._parse_set_interface_args(param[1:])
        except ValueError as exc:
            print(str(exc))
            return False
        changes = {
            "gateway": parsed["gateway"],
            "dns_nameservers": parsed["dns"] or None,
        }
        if parsed["ip"] is not None:
            try:
                value = ipaddress.IPv4Interface(parsed["ip"])
            except Exception:
                print("Invalid IP address format: {}".format(parsed["ip"]))
                return False
            changes["address"] = str(value.ip)
            changes["netmask"] = str(value.network.netmask)
        result = self._apply_mgt_transaction(restart=parsed["restart"], **changes)
        if not result:
            return False
        if parsed["restart"]:
            print("Management interface restarted successfully.")
            return True
        if self._mgt_last_changed:
            print("Configuration updated successfully.")
            print("Run 'set interface mgt restart' to apply the changes.")
        return True

    _SENSOR_IFACE_CFG_HINTS = {
        "mgt": ["01-mgt.cfg"],
        "host": ["01-host.cfg"],
        "hostmgmt": ["02-hostmgmt.cfg"],
        "data1g": ["01-data1g.cfg"],
        "data10g": ["10-data10g.cfg"],
    }

    def _uses_interfaces_d_source(self):
        main_path = "/etc/network/interfaces"
        if not os.path.exists(main_path):
            return os.path.isdir("/etc/network/interfaces.d")
        try:
            with open(main_path, 'r') as f:
                for line in f:
                    if re.match(r'^\s*source\s+/etc/network/interfaces\.d/\*', line):
                        return True
        except Exception:
            pass
        return False

    def _iface_defined_in_file(self, interface, path):
        if not path or not os.path.exists(path):
            return False
        try:
            with open(path, 'r') as f:
                for line in f:
                    if re.match(r'^\s*(auto|iface|allow-hotplug)\s+{}\b'.format(re.escape(interface)), line):
                        return True
        except Exception:
            return False
        return False

    def _find_iface_config_path(self, interface):
        """Return the config file that defines *interface*, or None."""
        interfaces_d = "/etc/network/interfaces.d"
        main_path = "/etc/network/interfaces"

        for name in self._SENSOR_IFACE_CFG_HINTS.get(interface, []):
            candidate = os.path.join(interfaces_d, name)
            if self._iface_defined_in_file(interface, candidate):
                return candidate

        if os.path.isdir(interfaces_d):
            for name in sorted(os.listdir(interfaces_d)):
                if not name.endswith('.cfg'):
                    continue
                candidate = os.path.join(interfaces_d, name)
                if self._iface_defined_in_file(interface, candidate):
                    return candidate

        if self._iface_defined_in_file(interface, main_path):
            return main_path
        return None

    def _default_iface_config_path(self, interface):
        """Return preferred write path when an interface block does not exist yet."""
        interfaces_d = "/etc/network/interfaces.d"
        hints = self._SENSOR_IFACE_CFG_HINTS
        if interface in hints and (os.path.isdir(interfaces_d) or self._uses_interfaces_d_source()):
            return os.path.join(interfaces_d, hints[interface][0])
        return "/etc/network/interfaces"

    def _write_iface_config_file_with_backup(self, path, contents):
        try:
            normalized = [line.rstrip("\n") for line in contents]
            _atomic_replace_text_file(path, "\n".join(normalized) + "\n")
            return True
        except Exception as e:
            print('Failed to update interface configuration')
            print(e)
            return False

    def _read_interface_config_lines(self, interface):
        cfg_path = self._find_iface_config_path(interface)
        if cfg_path:
            try:
                with open(cfg_path, 'r') as f:
                    return f.readlines()
            except Exception:
                return []
        return []

    def _interface_block_exists(self, interface):
        return self._find_iface_config_path(interface) is not None

    def _resolve_iface_config_name(self, interface):
        if not self.is_sensor_host_mode():
            return interface
        if interface == "host":
            if self._interface_block_exists(interface):
                return interface
            if self._interface_block_exists("hostmgmt"):
                return "hostmgmt"
        return interface

    def _netmask_to_cidr(self, netmask):
        try:
            packed = socket.inet_aton(netmask)
            bits = bin(struct.unpack("!I", packed)[0]).count("1")
            return bits
        except Exception:
            return None

    def _get_interface_expected_config(self, interface):
        config_interface = self._resolve_iface_config_name(interface)
        lines = self._read_interface_config_lines(config_interface)
        in_block = False
        address = None
        netmask = None
        dns_list = []
        for line in lines:
            if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(config_interface)), line):
                in_block = True
            elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                in_block = False
            if not in_block:
                continue
            addr_match = re.match(r'^\s*address\s+(\S+)', line)
            if addr_match:
                address = addr_match.group(1)
            netmask_match = re.match(r'^\s*netmask\s+(\S+)', line)
            if netmask_match:
                netmask = netmask_match.group(1)
            dns_match = re.match(r'^\s*dns-nameservers\s+(.+)', line)
            if dns_match:
                dns_list = [d for d in dns_match.group(1).strip().split() if self.valid_ipv4_address(d)]
        expected_ip = None
        if address:
            if netmask:
                cidr = self._netmask_to_cidr(netmask)
                if cidr is not None:
                    expected_ip = "{}/{}".format(address, cidr)
            if expected_ip is None:
                expected_ip = address
        return expected_ip, dns_list

    def _get_interface_netmask(self, interface):
        config_interface = self._resolve_iface_config_name(interface)
        lines = self._read_interface_config_lines(config_interface)
        in_block = False
        netmask = None
        for line in lines:
            if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(config_interface)), line):
                in_block = True
            elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                in_block = False
            if not in_block:
                continue
            netmask_match = re.match(r'^\s*netmask\s+(\S+)', line)
            if netmask_match:
                netmask = netmask_match.group(1)
        return netmask

    def _get_interface_gateway(self, interface):
        config_interface = self._resolve_iface_config_name(interface)
        lines = self._read_interface_config_lines(config_interface)
        in_block = False
        gateway = None
        for line in lines:
            if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(config_interface)), line):
                in_block = True
            elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                in_block = False
            if not in_block:
                continue
            gw_match = re.match(r'^\s*gateway\s+(\S+)', line)
            if gw_match:
                gateway = gw_match.group(1)
        return gateway

    def _ensure_interfaces_base(self):
        main_path = "/etc/network/interfaces"
        contents = []
        if os.path.exists(main_path):
            with open(main_path, 'r') as f:
                contents = f.read().splitlines()
        has_lo = any(re.match(r'^\s*iface\s+lo\s+inet\s+loopback', line) for line in contents)
        has_auto_lo = any(re.match(r'^\s*auto\s+lo\b', line) for line in contents)
        has_source = any(re.match(r'^\s*source\s+/etc/network/interfaces\.d/\*', line) for line in contents)
        changed = False

        if not has_auto_lo:
            contents.insert(0, "auto lo")
            changed = True
        if not has_lo:
            insert_at = 1 if contents and contents[0].strip() == "auto lo" else 0
            contents.insert(insert_at, "iface lo inet loopback")
            changed = True

        if os.path.isdir("/etc/network/interfaces.d") and not has_source:
            contents.append("source /etc/network/interfaces.d/*")
            changed = True

        if changed:
            self._write_interfaces_file_with_backup(contents)

    def _parse_iface_block(self, interface):
        config_interface = self._resolve_iface_config_name(interface)
        lines = self._read_interface_config_lines(config_interface)
        in_block = False
        mode = None
        address = None
        netmask = None
        dns_list = []
        block_lines = []
        for line in lines:
            if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(config_interface)), line):
                in_block = True
            elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                break
            if not in_block:
                continue
            block_lines.append(line.rstrip("\n"))
            iface_match = re.match(r'^\s*iface\s+{}\s+inet\s+(\S+)'.format(re.escape(config_interface)), line)
            if iface_match:
                mode = iface_match.group(1)
            addr_match = re.match(r'^\s*address\s+(\S+)', line)
            if addr_match:
                address = addr_match.group(1)
            netmask_match = re.match(r'^\s*netmask\s+(\S+)', line)
            if netmask_match:
                netmask = netmask_match.group(1)
            dns_match = re.match(r'^\s*dns-nameservers\s+(.+)', line)
            if dns_match:
                dns_list = [d for d in dns_match.group(1).strip().split() if self.valid_ipv4_address(d)]
        return mode, address, netmask, dns_list, block_lines

    def _write_interfaces_file_with_backup(self, contents):
        main_path = NETWORK_INTERFACES_PATH
        try:
            _atomic_replace_text_file(main_path, "\n".join(contents) + "\n")
            return True
        except Exception as e:
            print('Failed to update interface configuration')
            print(e)
            return False

    def _ensure_iface_stanza(self, interface, expected_ip, expected_dns):
        config_interface = self._resolve_iface_config_name(interface)
        mode, address, netmask, dns_list, block_lines = self._parse_iface_block(config_interface)
        if mode:
            if mode == "static" and (not address or not netmask):
                print("Invalid interface stanza for {}: static requires address/netmask".format(interface))
                for line in block_lines:
                    print(line)
                return False
            return True

        if not expected_ip:
            print("Missing interface stanza for {} and no expected IP available".format(interface))
            return False

        addr, netmask_str = self.cidr_to_netmask(expected_ip) if "/" in expected_ip else (expected_ip, None)
        if not addr or not netmask_str:
            print("Failed to build static stanza for {} from expected IP".format(interface))
            return False

        new_block = [
            "auto {}".format(config_interface),
            "iface {} inet static".format(config_interface),
            "address {}".format(addr),
            "netmask {}".format(netmask_str),
        ]
        if expected_dns:
            new_block.append("dns-nameservers {}".format(" ".join(expected_dns)))

        lines = self._read_interface_config_lines(config_interface)
        new_lines = [l.rstrip("\n") for l in lines]
        if new_lines and new_lines[-1].strip():
            new_lines.append("")
        return self.update_interface_file(config_interface, new_block)

    def _apply_interface_config(self, interface, ip=None, gateway=None, dns_list=None):
        if interface == "mgt":
            print("Management interface cannot be modified by the generic interface editor.")
            return False
        config_interface = self._resolve_iface_config_name(interface)
        lines = self._read_interface_config_lines(config_interface)
        if dns_list is None:
            dns_list = []

        start = None
        end = None
        in_block = False
        for idx, line in enumerate(lines):
            if re.match(r'^\s*(auto|iface)\s+{}\b'.format(re.escape(config_interface)), line):
                if start is None:
                    start = idx
                    in_block = True
            elif in_block and re.match(r'^\s*(auto|iface)\s+\S+', line):
                end = idx
                in_block = False
                break
        if start is not None and end is None:
            end = len(lines)

        existing_auto = False
        existing_mode = None
        existing_address = None
        existing_netmask = None
        existing_gateway = None
        existing_dns = []
        other_lines = []

        if start is not None:
            block_lines = lines[start:end]
            for line in block_lines:
                if re.match(r'^\s*auto\s+{}\b'.format(re.escape(config_interface)), line):
                    existing_auto = True
                    continue
                iface_match = re.match(r'^\s*iface\s+{}\s+inet\s+(\S+)'.format(re.escape(config_interface)), line)
                if iface_match:
                    existing_mode = iface_match.group(1)
                    continue
                addr_match = re.match(r'^\s*address\s+(\S+)', line)
                if addr_match:
                    existing_address = addr_match.group(1)
                    continue
                netmask_match = re.match(r'^\s*netmask\s+(\S+)', line)
                if netmask_match:
                    existing_netmask = netmask_match.group(1)
                    continue
                gw_match = re.match(r'^\s*gateway\s+(\S+)', line)
                if gw_match:
                    existing_gateway = gw_match.group(1)
                    continue
                dns_match = re.match(r'^\s*dns-nameservers\s+(.+)', line)
                if dns_match:
                    existing_dns = [d for d in dns_match.group(1).strip().split() if self.valid_ipv4_address(d)]
                    continue
                other_lines.append(line.rstrip())

        if ip:
            new_address, new_netmask = self.cidr_to_netmask(ip)
            if not new_address or not new_netmask:
                print('Invalid IP address format: {}'.format(ip))
                return False
            mode = "static"
        else:
            new_address = existing_address
            new_netmask = existing_netmask
            mode = existing_mode or "static"

        new_gateway = gateway if gateway is not None else existing_gateway
        new_dns = dns_list if dns_list else existing_dns

        if start is None and not ip and (new_gateway or new_dns):
            print('IP address is required to create a new interface configuration\n')
            return False

        if mode == "static" and not new_address:
            print('IP address is required for static configuration\n')
            return False

        new_block = []
        if existing_auto or start is None:
            new_block.append("auto {}".format(config_interface))
        new_block.append("iface {} inet {}".format(config_interface, mode))

        if mode != "dhcp":
            if new_address:
                new_block.append("address {}".format(new_address))
            if new_netmask:
                new_block.append("netmask {}".format(new_netmask))
            if new_gateway:
                new_block.append("gateway {}".format(new_gateway))
        if new_dns:
            new_block.append("dns-nameservers {}".format(" ".join(new_dns)))

        for line in other_lines:
            if not line:
                continue
            if re.match(r'^\s*source\s+/etc/network/interfaces\.d/\*', line):
                continue
            if re.match(r'^\s*iface\s+lo\s+inet\s+loopback', line):
                continue
            if re.match(r'^\s*auto\s+lo\b', line):
                continue
            new_block.append(line)

        if not self.update_interface_file(config_interface, new_block):
            return False
        if dns_list:
            keep_path = self._get_interface_config_target_path(config_interface)
            self._purge_interface_dns_from_other_files(config_interface, keep_path)
        return True

    def _get_interface_config_target_path(self, interface):
        cfg_path = self._find_iface_config_path(interface)
        if cfg_path:
            return cfg_path
        return self._default_iface_config_path(interface)

    def _purge_interface_dns_from_other_files(self, interface, keep_path):
        paths = []
        main_path = "/etc/network/interfaces"
        if os.path.exists(main_path):
            paths.append(main_path)
        interfaces_d_dir = "/etc/network/interfaces.d"
        if os.path.exists(interfaces_d_dir):
            for filename in os.listdir(interfaces_d_dir):
                if filename.endswith('.cfg'):
                    paths.append(os.path.join(interfaces_d_dir, filename))

        for path in paths:
            if path == keep_path:
                continue
            try:
                with open(path, 'r') as f:
                    lines = f.readlines()
            except Exception:
                continue
            current_interface = None
            updated = []
            changed = False
            for line in lines:
                iface_match = re.match(r'^\s*(auto|iface|allow-hotplug)\s+(\S+)', line)
                if iface_match:
                    current_interface = iface_match.group(2)
                if current_interface == interface and re.match(r'^\s*dns-nameservers\s+(.+)', line):
                    changed = True
                    continue
                updated.append(line)
            if changed:
                try:
                    _atomic_replace_text_file(path, "".join(updated))
                except Exception:
                    continue

    def set_interface_callback2(self, param):
        if not param or len(param) < 3:
            print("Usage: set interface <interface> <ip|gateway|dns|restart> <value>")
            return False
        interface = param[0]
        field = param[1].lower()
        if interface == "mgt" or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface):
            print("Invalid or protected interface name.")
            return False
        if not self.iface_exists(interface):
            print("Interface does not exist.")
            return False
        if field not in {"ip", "gateway", "dns", "restart"}:
            print("Invalid interface option.")
            return False
        try:
            cloud_init_file = Path("/etc/network/interfaces.d/50-cloud-init.cfg")
            if cloud_init_file.is_file():
                interfaces_path = Path("/etc/network/interfaces")
                with interfaces_path.open("a", encoding="utf-8") as target:
                    target.write("\n")
                    with cloud_init_file.open("r", encoding="utf-8") as source:
                        shutil.copyfileobj(source, target)
                cloud_init_file.unlink()

            value = param[2]
            network_mode = ""
            new_address = ""
            new_netmask = ""
            new_gateway = ""
            new_dns_server = ""
            new_restart = ""
            if field == "ip":
                if value.lower() == "dhcp":
                    network_mode = "dhcp"
                else:
                    parsed_ip = ipaddress.IPv4Interface(value)
                    network_mode = "static"
                    new_address = str(parsed_ip.ip)
                    new_netmask = str(parsed_ip.network.netmask)
            elif field == "gateway":
                new_gateway = str(ipaddress.IPv4Address(value))
            elif field == "dns":
                new_dns_server = " ".join(str(ipaddress.IPv4Address(item)) for item in param[2:])
            elif field == "restart":
                new_restart = value

            with open("/etc/network/interfaces", "r", encoding="utf-8") as conf_f:
                lines = conf_f.readlines()
            contents = []
            is_iface_config_block = False
            iface_exists = False
            iface_configured = False
            netmask_configured = False
            skip_non_existing = False
            auto_pattern = r"\s*auto {}\b.*".format(re.escape(interface))
            iface_pattern = r"\s*iface {}\s+.*".format(re.escape(interface))

            for line in lines:
                line = line.rstrip()
                auto_match = re.match(auto_pattern, line)
                iface_match = re.match(iface_pattern, line)
                current_iface = self.get_interface_from_line(line)
                if current_iface:
                    if not self.iface_exists(current_iface):
                        skip_non_existing = True
                        continue
                    skip_non_existing = False
                if skip_non_existing:
                    continue
                if auto_match or iface_match:
                    is_iface_config_block = True
                    iface_exists = True
                if is_iface_config_block:
                    if iface_match:
                        tokens = re.match(r"\s*iface\s+(\S+)\s+inet\s+(\S+).*", line)
                        raw_mode = tokens.group(2) if tokens else ""
                        if raw_mode == "static" and network_mode == "dhcp":
                            contents.append("iface {} inet dhcp".format(interface))
                            iface_configured = True
                        elif raw_mode == "dhcp" and network_mode == "static":
                            contents.append("iface {} inet static".format(interface))
                        else:
                            contents.append(line)
                            if raw_mode:
                                network_mode = raw_mode
                    elif auto_match:
                        contents.append(line)
                    elif re.match(r"\s*address\s+(.+)", line):
                        if network_mode == "dhcp":
                            continue
                        if new_address:
                            contents.append("address {}".format(new_address))
                            iface_configured = True
                        else:
                            contents.append(line)
                    elif re.match(r"\s*netmask\s+(.+)", line):
                        if network_mode == "dhcp":
                            continue
                        if new_netmask:
                            contents.append("netmask {}".format(new_netmask))
                            netmask_configured = True
                        else:
                            contents.append(line)
                    elif re.match(r"\s*gateway\s+(.+)", line):
                        if new_gateway:
                            contents.append("gateway {}".format(new_gateway))
                        elif field != "gateway":
                            contents.append(line)
                    elif re.match(r"\s*dns-nameservers\s+(.+)", line):
                        if new_dns_server:
                            contents.append("dns-nameservers {}".format(new_dns_server))
                        elif field != "dns":
                            contents.append(line)
                    else:
                        contents.append(line)
                else:
                    contents.append(line)

            if not iface_exists:
                contents.extend(["", "auto {}".format(interface)])
                if network_mode == "dhcp":
                    contents.append("iface {} inet dhcp".format(interface))
                else:
                    contents.append("iface {} inet static".format(interface))
                    if new_address:
                        contents.append("address {}".format(new_address))
                    if new_netmask:
                        contents.append("netmask {}".format(new_netmask))
                    if new_gateway:
                        contents.append("gateway {}".format(new_gateway))
                    if new_dns_server:
                        contents.append("dns-nameservers {}".format(new_dns_server))
            else:
                if network_mode == "static":
                    if new_address and not iface_configured:
                        contents.append("address {}".format(new_address))
                    if new_netmask and not netmask_configured:
                        contents.append("netmask {}".format(new_netmask))
                if new_gateway and not any(line.startswith("gateway ") for line in contents):
                    contents.append("gateway {}".format(new_gateway))
                if new_dns_server and not any(line.startswith("dns-nameservers ") for line in contents):
                    contents.append("dns-nameservers {}".format(new_dns_server))

            _atomic_replace_text_file("/etc/network/interfaces", "\n".join(contents).rstrip() + "\n")
            if field == "restart" or new_restart:
                return self.restart_network_manager(interface, new_address, new_netmask, new_gateway)
            print("Run 'set interface {} restart' command to apply the changes.\n".format(interface))
            return True
        except Exception as exc:
            print("Failed to update interface configuration: {}".format(exc))
            return False

    def set_interface_callback3(self, param):
        interface = param[0]
        field = param[1]
        value = param[2]
        current_address = ''
        current_netmask = ''
        current_gateway = ''
        new_address = ''
        new_netmask = ''
        new_gateway = ''
        current_contents = list()
        contents = list()
        is_ip_change = False
        is_gateway_change = False
        require_interface_restart = False

        if not self.is_device_exist(interface):
            return
        if field.lower() == 'ip':
            new_address, new_netmask = self.cidr_to_netmask(value)
            is_ip_change = True
        if field.lower() == 'gateway':
            new_gateway = value
            is_gateway_change = True
        elif field.lower() == "restart":
            new_restart = value
            require_interface_restart = True

        if interface == 'data1g':
            try:
                with open("/etc/network/interfaces.d/01-data1g.cfg", 'r') as f:
                    current_contents = f.readlines()
            except Exception as e: 
                print(e)
                return
        if interface == 'data10g':
            try:
                with open("/etc/network/interfaces.d/10-data10g.cfg", 'r') as f:
                    current_contents = f.readlines()
            except Exception as e:
                print(e)
                return

        for line in current_contents:
            if re.match('\s*address\s+.*', line):
                current_address = re.match('\s*address\s+(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})', line).group(1)
            if re.match('\s*netmask\s+.*', line):
                current_mask = re.match('\s*netmask\s+(\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3})', line).group(1)

        if is_ip_change:
            contents.append('auto {}'.format(interface))
            contents.append('iface {} inet static'.format(interface)) 
            contents.append('address {}'.format(new_address))
            contents.append('netmask {}'.format(new_netmask))
            if not self.update_interface_file(interface, contents):
                return

        elif is_gateway_change:
            if not current_address or not current_mask: 
                print('Please configure IP address and netmask before configuring "{}" interface gateway'.format(interface))
                print('set interface {} ip <IP Address/Netmask>\n'.format(interface))
                return
            self.update_dp_mgt_data(new_gateway, interface) 

        elif require_interface_restart:
             print("Restarting network interface. You need to use new IP address to reconnect...\n")
             self._restart_interface_with_verification(interface)

        if not (field.lower() == "restart"):
             print("Run 'set interface {0} restart' command to apply the changes.\n".format(interface))

        return None

    def _restart_interface_with_verification(self, interface):
        if interface == "mgt":
            return self._restart_mgt_interface()
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface or "") or not self.is_device_exist(interface):
            print("Invalid interface name.")
            return False
        expected_ip, expected_dns = self._get_interface_expected_config(interface)
        expected_gateway = self._get_interface_gateway(interface)
        self._ensure_interfaces_base()
        if not self._ensure_iface_stanza(interface, expected_ip, expected_dns):
            return False
        dry_run = subprocess.run(
            ["ifup", "--no-act", interface],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, check=False,
        )
        if dry_run.returncode != 0:
            print("ifup dry-run failed for {}".format(interface))
            print("returncode: {}".format(dry_run.returncode))
            if dry_run.stdout:
                print("stdout: {}".format(dry_run.stdout.strip()))
            if dry_run.stderr:
                print("stderr: {}".format(dry_run.stderr.strip()))
            return False
        if not self.restart_new_network_manager(interface, expected_ip=expected_ip, expected_dns=expected_dns):
            return False
        if expected_gateway and self.is_sensor_host_mode():
            if not self._ensure_host_gateway(interface, expected_gateway):
                return False
        print("Restart completed.\n")
        return True

    def _ensure_host_gateway(self, interface, gateway):
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface or ""):
            return False
        try:
            gateway = str(ipaddress.IPv4Address(gateway))
        except ValueError:
            return False
        def current_gateway():
            proc = subprocess.run(
                ["ip", "route", "show", "default"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                text=True, check=False,
            )
            if proc.returncode != 0:
                return None
            for line in proc.stdout.splitlines():
                match = re.search(r"\bdefault\s+via\s+(\d+\.\d+\.\d+\.\d+)\s+dev\s+([A-Za-z0-9_.:-]{1,15})", line)
                if match:
                    return match.group(1), match.group(2)
            return None
        if current_gateway() == (gateway, interface):
            return True
        set_proc = subprocess.run(
            ["ip", "route", "replace", "default", "via", gateway, "dev", interface],
            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            text=True, check=False,
        )
        if set_proc.returncode != 0:
            print("Failed to apply host gateway: {}".format((set_proc.stderr or set_proc.stdout).strip()))
            return False
        if current_gateway() == (gateway, interface):
            return True
        print("Failed to verify host default gateway")
        return False

    def restart_new_network_manager(self, interface, expected_ip=None, expected_dns=None):
        if interface == "mgt":
            return self._restart_mgt_interface()
        if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface or "") or not self.is_device_exist(interface):
            print("Invalid interface name.")
            return False
        try:
            if expected_ip:
                expected_ip = str(ipaddress.IPv4Interface(expected_ip))
            if expected_dns:
                expected_dns = [str(ipaddress.IPv4Address(value)) for value in expected_dns]
            dhclient_file = Path("/run/resolvconf/interface") / "{}.dhclient".format(interface)
            try:
                if dhclient_file.is_file() or dhclient_file.is_symlink():
                    dhclient_file.unlink()
            except FileNotFoundError:
                pass
            flush_proc = subprocess.run(
                ["ip", "address", "flush", "dev", interface],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if flush_proc.returncode != 0:
                print("Failed to restart networking! {}".format((flush_proc.stderr or flush_proc.stdout).strip()))
                return False
            subprocess.run(["ifdown", interface], stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False)
            up_proc = subprocess.run(
                ["ifup", interface],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
            )
            if up_proc.returncode != 0:
                err_text = "{}\n{}".format(up_proc.stdout or "", up_proc.stderr or "")
                if not (expected_ip and ("File exists" in err_text or "Address already assigned" in err_text)):
                    print("Failed to restart networking!")
                    print("returncode: {}".format(up_proc.returncode))
                    if up_proc.stdout:
                        print("stdout: {}".format(up_proc.stdout.strip()))
                    if up_proc.stderr:
                        print("stderr: {}".format(up_proc.stderr.strip()))
                    return False
                print("Warning: ifup returned address already assigned; continuing with state verification")
            def current_ipv4():
                result = subprocess.run(
                    ["ip", "-4", "addr", "show", "dev", interface],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
                )
                if result.returncode != 0:
                    return []
                return re.findall(r"\binet\s+(\d+\.\d+\.\d+\.\d+/\d+)", result.stdout)
            inet_lines = current_ipv4()
            if not inet_lines and expected_ip:
                add_proc = subprocess.run(
                    ["ip", "-4", "addr", "add", expected_ip, "dev", interface],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
                )
                if add_proc.returncode != 0:
                    print("Failed to recover IP address on {}: {}".format(interface, (add_proc.stderr or add_proc.stdout).strip()))
                    return False
                inet_lines = current_ipv4()
                if len(inet_lines) != 1 or expected_ip not in inet_lines:
                    print("Failed to verify IPv4 address count on {} after recovery".format(interface))
                    return False
            if len(inet_lines) > 1:
                if not expected_ip:
                    print("Multiple IPv4 addresses detected on {} after restart".format(interface))
                    return False
                subprocess.run(
                    ["ip", "-4", "addr", "flush", "dev", interface],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
                )
                add_proc = subprocess.run(
                    ["ip", "-4", "addr", "add", expected_ip, "dev", interface],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=False,
                )
                if add_proc.returncode != 0:
                    print("Failed to recover IP address on {}: {}".format(interface, (add_proc.stderr or add_proc.stdout).strip()))
                    return False
                inet_lines = current_ipv4()
                if len(inet_lines) != 1 or expected_ip not in inet_lines:
                    print("Failed to verify IPv4 address count on {} after recovery".format(interface))
                    return False
            if expected_ip and expected_ip not in current_ipv4():
                print("Failed to verify IP address on {} after restart".format(interface))
                return False
            if expected_dns:
                current_dns = self._get_interface_expected_config(interface)[1]
                if not set(expected_dns).issubset(set(current_dns)):
                    print("Failed to verify DNS settings on {} after restart".format(interface))
                    return False
            return True
        except Exception as exc:
            print("Failed to restart networking! {}".format(exc))
            return False

    def restart_network_manager(interface, address, netmask, new_gateway):
        try:
            if not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface or ""):
                return False
            if address:
                address = str(ipaddress.IPv4Address(address))
                netmask = str(ipaddress.IPv4Address(netmask))
                first = subprocess.run(
                    ["ifconfig", interface, "0.0.0.0"],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                )
                if first.returncode != 0:
                    return False
                second = subprocess.run(
                    ["ifconfig", interface, address, "netmask", netmask],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                )
                if second.returncode != 0:
                    return False
            elif new_gateway:
                new_gateway = str(ipaddress.IPv4Address(new_gateway))
                subprocess.run(["ip", "route", "del", "default"], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
                gateway_result = subprocess.run(
                    ["ip", "route", "add", "default", "via", new_gateway],
                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
                )
                if gateway_result.returncode != 0:
                    return False
            restart = subprocess.run(
                ["/etc/init.d/networking", "restart"],
                stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False,
            )
            return restart.returncode == 0
        except Exception:
            print("Failed to restart networking!")
            return False

    def is_device_exist(self, interface):
        if not isinstance(interface, str) or not re.fullmatch(r"[A-Za-z0-9_.:-]{1,15}", interface):
            print("Invalid interface name.")
            return False

        result = subprocess.run(
            ["ip", "link", "show", "dev", interface],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            print('Device "{}" does not exist. Is it used by other virtual machine?'.format(interface))
            return False
        return True


    def set_interface_callback(self, key, param):
        filtered = [p for p in param if p != ""]
        if filtered and filtered[0].rstrip("?") == "mgt":
            if filtered[0].endswith("?") or len(filtered) == 1:
                print('\nip <IP Address/Netmask>   Specify interface IP address and netmask')
                print('gateway <IP Address>      Specify default gateway IP address')
                print('dns <IP Address> [...]    Specify DNS server IP address(es)')
                print('restart                   Restart network interface\n')
                return
            self._set_mgt_interface(filtered)
            return
        if self.is_sensor_host_mode():
            self.set_interface_sensor(param)
            return

        self._debug_print("DEBUG set interface param={}".format(param))
        param = [p for p in param if p != '']

        if not param or param[0].endswith('?') or len(param) <= 4:
            if (len(param) < 1 or (len(param) == 1 and param[0] == '?')) or \
                (len(param) == 1 and not re.match('mgt|data1[0]?g', param[0])) or \
                (len(param) == 2 and not re.match('mgt|data1[0]?g', param[0]) and param[1] == '?'):
                print('\n<Interface Name>  Specify a supported interface name (mgt, data1g, data10g)\n')
                return
            elif (len(param) == 1 and re.match('mgt', param[0])) or \
                (len(param) == 1 and re.match('mgt[?]', param[0])) or \
                (len(param) == 2 and re.match('mgt', param[0]) and param[1] == '?'):
                print('\nip <IP Address/Netmask>   Specify interface IP address and netmask')
                print('gateway <IP Address>      Specify default gateway IP address')
                print('dns <IP Address> [...]    Specify single DNS server IP address or multiple DNS separated by space')
                print('restart                   Restart network interface\n')
                return
            elif (len(param) == 1 and re.match('data1[0]?g', param[0])) or \
                (len(param) == 1 and re.match('data1[0]?g[?]', param[0])) or \
                (len(param) == 2 and re.match('data1[0]?g', param[0]) and param[1] == '?'):
                print('\nip <IP Address/Netmask>   Specify interface IP address and netmask')
                print('gateway <IP Address>      Specify default gateway IP address')
                print('restart                   Restart network interface\n')
                return
            elif len(param) == 2 and not re.match('ip|gateway|dns|restart', param[1]):
                print('Invalid option: Available options are "ip", "gateway", "dns" and "restart"')
                print('\nip <IP Address/Netmask>   Specify interface IP address and netmask')
                print('dns <IP Address> [...]    Specify DNS server IP address or addresses separated by space')
                print('gateway <IP Address>      Specify default gateway IP address')
                print('restart                   Restart network interface\n')
                return
            elif (len(param) == 2 and param[1].endswith('ip?')) or \
                (len(param) == 3 and param[1] == 'ip' and not self.valid_ipv4_address(param[2].rstrip('?'))):
                print('\n<IP Address/Netmask>   Specify interface IP address and netmask\n')
                return
            elif (len(param) == 2 and param[1].endswith('gateway?')) or \
                (len(param) == 3 and param[1] == 'gateway' and not self.valid_ipv4_address(param[2].rstrip('?'))):
                print('\n<IP Address>      Specify default gateway IP address\n')
                return
            elif (len(param) == 2 and param[1].endswith('dns?')) or \
                (len(param) == 3 and param[1] == 'dns' and param[2].endswith('?')):
                print('\n<IP Address> [...]    Specify DNS server IP address or addresses separated by space\n')
                return
            elif (len(param) == 2 and param[1].endswith('restart?')) or \
                (len(param) == 3 and param[1] == 'restart' and param[2].endswith('?')):
                print('\nPress [Enter]\n')
                return
            elif (len(param) == 3 and param[1] == 'ip' and self.valid_ipv4_address(param[2].rstrip('?')) and param[2].endswith('?')) or \
                (len(param) == 4 and param[1] == 'ip' and self.valid_ipv4_address(param[2]) and param[3] == '?'):
                print('\nPress [Enter]\n')
                return
            elif (len(param) == 3 and param[1] == 'gateway' and self.valid_ipv4_address(param[2].rstrip('?')) and param[2].endswith('?')) or \
                (len(param) == 4 and param[1] == 'gateway' and self.valid_ipv4_address(param[2]) and param[3] == '?'):
                if not (re.match('^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', param[2]) or \
                    re.match('^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', param[2].rstrip('?'))):
                    print('Invalid gateway IP address format:')
                    print('\n<IP Address>      Specify default gateway IP address\n')
                    return
                print('\nPress [Enter]\n') 
                return

        interface = param[0]
        option = param[1]
        try:
            ip_address = param[2]
        except Exception:
            ip_address = ''
            param.append('')

        supported_interfaces = ['mgt', 'data1g', 'data10g']
        if interface not in supported_interfaces:
            # Allow user-selected interfaces without hardcoding
            self.set_interface_sensor(param)
            return
        # DP Appliance does NOT support dhcp on any interfaces
        #if option == 'dns' and (interface == 'data0'):
        #    print('Invalid option: only "mgt" interface support dns option')
        #    return

        if not self.is_device_exist(interface):
           return

        if len(param) >= 2 and param[1] == 'restart':
            print('Restarting network interface. You need to use new IP address to reconnect...\n')
            self._restart_interface_with_verification(interface)
            return

        tokens = [t for t in param[1:]]
        keywords = [t.lower() for t in tokens if t.lower() in {"ip", "gateway", "dns", "restart"}]
        if len(keywords) > 1 or ("restart" in keywords and len(tokens) > 1):
            try:
                parsed = self._parse_set_interface_args(tokens)
            except ValueError as e:
                print('{}\n'.format(e))
                return

            if parsed["ip"]:
                if parsed["ip"] == 'dhcp':
                    print("Invalid ip option: DHCP client is not supported")
                    return
                if '/' not in parsed["ip"] and self.valid_ipv4_address(parsed["ip"]):
                    print('Please specify network mask: {0}'.format(parsed["ip"]))
                    return
                if not self.valid_ipv4_address(parsed["ip"]) or '/' not in parsed["ip"]:
                    print('Invalid IP address format: {0}'.format(parsed["ip"]))
                    return
            if parsed["gateway"]:
                if not self.valid_ipv4_address(parsed["gateway"]) or '/' in parsed["gateway"]:
                    print('Invalid gateway IP address format: {0}'.format(parsed["gateway"]))
                    return
            if parsed["dns"]:
                if interface != 'mgt':
                    print('Invalid option: Only "mgt" interface support dns option')
                    return
                for dns in parsed["dns"]:
                    if not self.valid_ipv4_address(dns):
                        print('Invalid DNS server IP address format: {0}'.format(dns))
                        return

            if not self._apply_interface_config(
                interface,
                ip=parsed["ip"],
                gateway=parsed["gateway"],
                dns_list=parsed["dns"],
            ):
                return

            if parsed["restart"]:
                print('Restarting network interface. You need to use new IP address to reconnect...\n')
                if not self._restart_interface_with_verification(interface):
                    return
            else:
                print("Run 'set interface {0} restart' command to apply the changes.\n".format(interface))
            return

        if option != 'ip' and option != 'gateway' and option != 'dns' and option != 'restart':
            print('Invalid option: {0}'.format(option))
            return
        if option == 'ip':
            #if ip_address != 'dhcp' and len(ip_address.split('.')) < 4:
            if ip_address != 'dhcp' and '/' not in ip_address and self.valid_ipv4_address(ip_address):
                print('Please specify network mask: {0}'.format(ip_address))
                return
            if ip_address != 'dhcp' and not self.valid_ipv4_address(ip_address):
                print('Invalid IP address format: {0}'.format(ip_address))
                return
            if ip_address != 'dhcp' and ip_address.find('/') < 0:
                print('Please specify network mask: {0}'.format(ip_address))
                return
            if ip_address == 'dhcp':
                print("Invalid ip option: DHCP client is not supported")
                return
        if option == 'gateway':
            gw_address = param[2]
            if not self.valid_ipv4_address(gw_address) or not re.match('^\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}$', gw_address):
                print('Invalid gateway IP address format: {0}'.format(gw_address))
                print('\n<IP Address>      Specify default gateway IP address\n')
                return
        if option == 'dns':
            dns_address = param[2:]
            exist_valid_dns_ip = 0
            if interface == 'data1g' or interface == 'data10g':
                print('Invalid option: Only "mgt" interface support dns option')
                return
            for i in range(0,len(dns_address)):
                if self.valid_ipv4_address(dns_address[i]):
                    exist_valid_dns_ip = 1
                elif dns_address[i] == '?' and exist_valid_dns_ip == 1:
                    print('\nPress [Enter]\n')
                    return
                elif not self.valid_ipv4_address(dns_address[i]):
                    print('Invalid DNS server IP address format: {0}'.format(dns_address[i]))
                    return

        if not interface == 'mgt':
            self.set_interface_callback3(param)
            return
        self.set_interface_callback2(param)

    def valid_ipv4_address(self, address):
        if '/' in address:
            a = address.split('/')
            if len(a[0].split('.')) < 4 or len(a[0].split('.')) > 4: 
                return
            m1 = re.match(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$", a[0])
            if len(a[0].split('.')) == 4 and '.' in a[1]:
                if len(a[1].split('.')) < 4 or len(a[1].split('.')) > 4:
                    return
                elif len(a[1].split('.')) == 4 and a[1].endswith('?'):
                    m2 = re.match(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$", a[1].strip('?'))
                    return bool(m1) and all(map(lambda n: 0 <= int(n) <= 255, m1.groups())) and \
                        bool(m2) and all(map(lambda n: 0 <= int(n) <= 255, m2.groups()))
                elif len(a[1].split('.')) == 4:
                    m2 = re.match(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$", a[1])
                    return bool(m1) and all(map(lambda n: 0 <= int(n) <= 255, m1.groups())) and \
                        bool(m2) and all(map(lambda n: 0 <= int(n) <= 255, m2.groups()))

            if len(a[0].split('.')) == 4 and len(a[1]) == 2:
                m3 = re.match(r"^(\d{1,2})$", a[1])
                return bool(m1) and all(map(lambda n: 0 <= int(n) <= 255, m1.groups())) and \
                    bool(m3) and all(map(lambda n: 0 <= int(n) <= 32, m3.groups()))
            if len(a[0].split('.')) == 4 and len(a[1]) == 3 and a[1].endswith('?'):
                m3 = re.match(r"^(\d{1,2})$", a[1].strip('?'))
                return bool(m1) and all(map(lambda n: 0 <= int(n) <= 255, m1.groups())) and \
                    bool(m3) and all(map(lambda n: 0 <= int(n) <= 32, m3.groups()))
        else:
            if len(address.split('.')) < 4 or len(address.split('.')) > 4:
                return
            elif len(address.split('.')) == 4:
                m = re.match(r"^(\d{1,3})\.(\d{1,3})\.(\d{1,3})\.(\d{1,3})$", address)
                return bool(m) and all(map(lambda n: 0 <= int(n) <= 255, m.groups()))
         
    def complete_set_interface(self, text, line, begidx, endidx):
        options = ['ip', 'gateway', 'dns', 'restart']
        prefix_tokens = line[:begidx].split()
        # Expect: set interface <iface> [option]
        if len(prefix_tokens) >= 3:
            completion_set = options
        else:
            completion_set = self._get_interface_completion_list()

        if not text:
            completions = completion_set
        else:
            completions = [f for f in completion_set if f.startswith(text)]
        return completions

    def complete_unset_interface(self, text, line, begidx, endidx):
        options = ['ip', 'gateway', 'restart']
        prefix_tokens = line[:begidx].split()
        # Expect: unset interface <iface> [option]
        if len(prefix_tokens) >= 3:
            completion_set = options
        else:
            completion_set = self._get_interface_completion_list()

        if not text:
            completions = completion_set
        else:
            completions = [f for f in completion_set if f.startswith(text)]
        return completions

    def complete_show_interface(self, text, line, begidx, endidx):
        completion_set = self._get_interface_completion_list()
        if not text:
            return completion_set
        return [f for f in completion_set if f.startswith(text)]

    def _get_interface_completion_list(self):
        interfaces = os.listdir('/sys/class/net/')
        if 'virbr0' in interfaces:
            interfaces.remove('virbr0')
        if 'virbr0-nic' in interfaces:
            interfaces.remove('virbr0-nic')
        # Allow CLI aliases even if not kernel interfaces
        try:
            if self._interface_block_exists("host") or self._interface_block_exists("hostmgmt"):
                interfaces.append("host")
            if self._interface_block_exists("hostmgmt"):
                interfaces.append("hostmgmt")
        except Exception:
            pass
        return interfaces

    def complete_set(self, text, line, begidx, endidx):
        if not text and not line.startswith('set'):
            completions = self.set_command_help.keys()
        elif line.startswith('set interface'):
            return self.complete_set_interface(text, line, begidx, endidx)
        elif line.startswith('set dns'):
            return self.complete_set_dns(text, line, begidx, endidx)
        else:
            completions = [f for f in self.set_command_help.keys() if f.startswith(text)]
        return completions

    def complete_set_dns(self, text, line, begidx, endidx):
        tokens = line.split()
        # Expect: set dns <iface> [dns...]
        if len(tokens) <= 2:
            completion_set = self._get_interface_completion_list()
        else:
            # DNS values are free-form IPs; no safe completion
            completion_set = []
        if not text:
            return completion_set
        return [f for f in completion_set if f.startswith(text)]

    def complete_monitor(self, text, line, begidx, endidx):
        """Tab completion for monitor command"""
        if not text:
            completions = self.monitor_command_help.keys()
        elif line.startswith('monitor vm'):
            # Handle 'monitor vm htop <vm>'
            parts = line.split()
            if len(parts) == 3 and parts[2] == 'htop':
                # Complete VM names for htop
                vm_list = self.get_vm_list()
                if not text:
                    return vm_list
                return [vm for vm in vm_list if vm.startswith(text)]
            elif len(parts) == 2:
                # Complete subcommands after 'monitor vm'
                if not text:
                    return ['htop']
                return ['htop'] if 'htop'.startswith(text) else []
            else:
                completions = [f for f in self.monitor_command_help.keys() if f.startswith(text)]
        else:
            completions = [f for f in self.monitor_command_help.keys() if f.startswith(text)]
        return completions


    # Check to see whether service port opened or not
    def service_is_running(self, service_port):
        try:
            port = int(service_port)
        except (TypeError, ValueError):
            return 0
        if not 1 <= port <= 65535:
            return 0
        proc = subprocess.run(
            ["ss", "-lntH"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if proc.returncode != 0:
            return 0
        return sum(
            1 for line in proc.stdout.splitlines()
            if len(line.split()) >= 4 and line.split()[3].endswith(":{}".format(port))
        )

    def run_command_with_stderr(self, cmd):
        """Run an argv-only command. Shell command strings are intentionally rejected."""
        if not isinstance(cmd, (list, tuple)) or not cmd or any(not isinstance(item, str) for item in cmd):
            return False, "Only explicit argv command lists are supported."
        try:
            proc = subprocess.run(
                list(cmd),
                stdout=subprocess.PIPE,
                stderr=subprocess.PIPE,
                check=False,
            )
            if proc.returncode != 0:
                return False, proc.stderr or proc.stdout
            return True, proc.stdout
        except Exception as exc:
            return False, str(exc)

    # Execute shell command
    def shell_cmd_exec(self, line, crlf=True):
        """Execute an internal fixed command without invoking a shell."""
        try:
            argv = list(line) if isinstance(line, (list, tuple)) else shlex.split(line)
        except (TypeError, ValueError) as exc:
            print("Invalid internal command: {}".format(exc))
            return False
        if not argv or any(token in {";", "&&", "||", "|", ">", ">>", "<"} for token in argv):
            print("Shell operators are not accepted by internal command execution.")
            return False
        proc = subprocess.run(argv, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=False)
        if proc.stdout:
            output = proc.stdout.strip().decode("utf-8", errors="replace")
            if crlf:
                print("\n{}\n".format(output))
            else:
                print("{}".format(output))
        return proc.returncode == 0

    def system_is_container(self):
        try:
            cgroup = Path("/proc/1/cgroup").read_text(encoding="utf-8", errors="ignore")
            return "docker" in cgroup or "kubepods" in cgroup
        except OSError:
            return False

    def system_is_container(self):
        try:
            cgroup = Path("/proc/1/cgroup").read_text(encoding="utf-8", errors="ignore")
            return "docker" in cgroup or "kubepods" in cgroup
        except OSError:
            return False

def bytes2human(n):
    """
    >>> bytes2human(10000)
    '9K'
    >>> bytes2human(100001221)
    '95M'
    """
    symbols = ('K', 'M', 'G', 'T', 'P', 'E', 'Z', 'Y')
    prefix = {}
    for i, s in enumerate(symbols):
        prefix[s] = 1 << (i + 1) * 10
    for s in reversed(symbols):
        if n >= prefix[s]:
            value = int(float(n) / prefix[s])
            return '%s%s' % (value, s)
    return "%sB" % n


def main():
    signal.signal(signal.SIGINT, signal_handler)
    AellaCli().cmdloop()


if __name__ == '__main__':
    main()