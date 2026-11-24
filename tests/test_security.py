import tempfile
import types
import unittest
from pathlib import Path
from unittest import mock

import appliance_cli as module


class ShellDiagnosticPolicyTests(unittest.TestCase):
    def setUp(self):
        self.cli = module.AellaCli.__new__(module.AellaCli)

    def test_read_only_ip_queries_remain_available(self):
        for tokens in (
            ["ip", "-br", "addr"],
            ["ip", "link", "show", "dev", "eth0"],
            ["ip", "route", "get", "192.0.2.1"],
            ["ip", "netns", "list"],
        ):
            with self.subTest(tokens=tokens):
                self.assertTrue(self.cli._is_safe_shell_diagnostic(tokens))

    def test_ip_netns_exec_and_mutations_are_rejected(self):
        for tokens in (
            ["ip", "netns", "exec", "review", "/usr/bin/id"],
            ["ip", "link", "set", "eth0", "down"],
            ["ip", "route", "add", "default", "via", "192.0.2.1"],
        ):
            with self.subTest(tokens=tokens):
                self.assertFalse(self.cli._is_safe_shell_diagnostic(tokens))

    def test_tcpdump_postrotate_and_root_file_write_are_rejected(self):
        self.assertFalse(
            self.cli._is_safe_shell_diagnostic(
                ["tcpdump", "-G", "60", "-w", "capture.pcap", "-z", "/bin/sh"]
            )
        )
        self.assertFalse(
            self.cli._is_safe_shell_diagnostic(["tcpdump", "-w", "/etc/sudoers"])
        )
        self.assertTrue(
            self.cli._is_safe_shell_diagnostic(["tcpdump", "-i", "any", "port", "53"])
        )

    def test_dmesg_read_clear_is_rejected(self):
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["dmesg", "--ctime"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["dmesg", "--clear"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["dmesg", "-c"]))

    def test_iptables_mutation_is_rejected_but_listing_remains_available(self):
        self.assertTrue(
            self.cli._is_safe_shell_diagnostic(
                ["iptables", "-t", "nat", "-L", "-n", "-v"]
            )
        )
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["iptables", "-S"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["iptables", "-F"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["iptables", "-A", "INPUT", "-j", "ACCEPT"]))

    def test_interface_mutations_are_rejected(self):
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["ifconfig", "eth0"]))
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["ifconfig", "-a"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ifconfig", "eth0", "down"]))

    def test_top_requires_noninteractive_batch_mode(self):
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["top", "-b", "-n", "1"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["top"]))

    def test_cmd_exclamation_path_rejects_ip_netns_exec(self):
        import cmd
        cmd.Cmd.__init__(self.cli)
        self.cli.shell_command = ["ping", "tcpdump", "traceroute", "ifconfig", "iptables", "dmesg", "ip", "dig", "htop", "top"]
        with mock.patch.object(module.subprocess, "call") as call:
            self.cli.onecmd("!ip netns exec review /usr/bin/id")
        call.assert_not_called()

    def test_cmd_exclamation_path_keeps_read_only_ip(self):
        import cmd
        cmd.Cmd.__init__(self.cli)
        self.cli.shell_command = ["ping", "tcpdump", "traceroute", "ifconfig", "iptables", "dmesg", "ip", "dig", "htop", "top"]
        with mock.patch.object(module.subprocess, "call", return_value=0) as call:
            self.cli.onecmd("!ip -br addr")
        call.assert_called_once_with(["ip", "-br", "addr"], shell=False)


class InputValidationTests(unittest.TestCase):
    def setUp(self):
        self.cli = module.AellaCli.__new__(module.AellaCli)

    def test_time_injection_is_rejected_before_execution(self):
        with mock.patch.object(self.cli, "run_command_with_stderr") as run:
            self.cli.set_time_callback("time", ["2026-10-28", "08:00:00$(/usr/bin/id)"])
        run.assert_not_called()

    def test_valid_time_uses_fixed_argv(self):
        with mock.patch.object(self.cli, "run_command_with_stderr", return_value=(True, b"ok")) as run:
            self.cli.set_time_callback("time", ["2026-10-28", "08:00:00"])
        run.assert_called_once_with(["sudo", "date", "-s", "2026-10-28 08:00:00"])

    def test_package_injection_is_rejected(self):
        with mock.patch.object(self.cli, "run_command_with_stderr") as run:
            self.cli.set_patches_callback("patches", ["safe-pkg;id"])
        run.assert_not_called()

    def test_package_install_uses_argv(self):
        with mock.patch.object(
            self.cli, "run_command_with_stderr", return_value=(True, b"")
        ) as run:
            self.cli.set_patches_callback("patches", ["curl", "jq"])
        self.assertEqual(
            [call.args[0] for call in run.call_args_list],
            [
                ["sudo", "apt", "-qq", "update"],
                ["sudo", "apt", "-qqy", "install", "curl", "jq"],
                ["sudo", "apt", "clean"],
            ],
        )

    def test_patch_path_traversal_is_rejected(self):
        with mock.patch.object(self.cli, "run_command_with_stderr") as run:
            self.cli.set_patches_callback("patches", ["apply", "../../etc/cron.d/payload.deb"])
        run.assert_not_called()

    def test_interface_name_is_passed_as_argv(self):
        with mock.patch.object(
            module.subprocess,
            "run",
            return_value=types.SimpleNamespace(returncode=0, stdout="", stderr=""),
        ) as run:
            self.assertTrue(self.cli.is_device_exist("eth0"))
        run.assert_called_once()
        self.assertEqual(run.call_args.args[0], ["ip", "link", "show", "dev", "eth0"])
        self.assertFalse(run.call_args.kwargs.get("shell", False))

    def test_interface_shell_injection_is_rejected(self):
        with mock.patch.object(module.subprocess, "run") as run:
            self.assertFalse(self.cli.is_device_exist("eth0;id"))
        run.assert_not_called()


class SystemPasswordTests(unittest.TestCase):
    def test_invoking_user_is_resolved_from_sudo_uid(self):
        with mock.patch.object(module.os, "geteuid", return_value=0), \
             mock.patch.dict(module.os.environ, {"SUDO_UID": "1000", "SUDO_USER": "stellar"}, clear=True), \
             mock.patch.object(module.pwd, "getpwuid", return_value=types.SimpleNamespace(pw_name="stellar")):
            self.assertEqual(module._get_invoking_username(), "stellar")

    def test_mismatched_sudo_identity_fails_closed(self):
        with mock.patch.object(module.os, "geteuid", return_value=0), \
             mock.patch.dict(module.os.environ, {"SUDO_UID": "1000", "SUDO_USER": "aella"}, clear=True), \
             mock.patch.object(module.pwd, "getpwuid", return_value=types.SimpleNamespace(pw_name="stellar")):
            self.assertIsNone(module._get_invoking_username())

    def test_unix_account_password_verification_uses_shadow_hash(self):
        stored_hash = "$6$rounds=5000$test$examplehash"
        with tempfile.TemporaryDirectory() as temp_dir:
            shadow_path = Path(temp_dir) / "shadow"
            shadow_path.write_text("stellar:{}:1:0:99999:7:::\n".format(stored_hash))
            fake_libcrypt = mock.Mock()
            fake_libcrypt.crypt.return_value = stored_hash.encode("utf-8")
            with mock.patch.object(module.pwd, "getpwnam", return_value=types.SimpleNamespace(pw_uid=1000)), \
                 mock.patch.object(module.ctypes.util, "find_library", return_value="libcrypt.so.1"), \
                 mock.patch.object(module.ctypes, "CDLL", return_value=fake_libcrypt):
                self.assertTrue(
                    module._verify_system_account_password("stellar", "correct", str(shadow_path))
                )
            fake_libcrypt.crypt.assert_called_once_with(b"correct", stored_hash.encode("utf-8"))

    def test_locked_or_missing_shadow_password_fails_closed(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            shadow_path = Path(temp_dir) / "shadow"
            shadow_path.write_text("stellar:!$6$locked:1:0:99999:7:::\n")
            with mock.patch.object(module.pwd, "getpwnam", return_value=types.SimpleNamespace(pw_uid=1000)), \
                 mock.patch.object(module.ctypes, "CDLL") as load_crypt:
                self.assertFalse(
                    module._verify_system_account_password("stellar", "anything", str(shadow_path))
                )
            load_crypt.assert_not_called()

    def test_embedded_shell_password_hash_is_removed(self):
        source = Path(module.__file__).read_text(encoding="utf-8")
        self.assertNotIn("0238b57cd42b4aa6b85991ea28702133", source)
        self.assertNotIn("hashlib.md5", source)


if __name__ == "__main__":
    unittest.main()
