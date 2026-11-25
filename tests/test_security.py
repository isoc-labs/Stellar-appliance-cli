import ast
import cmd
import inspect
import io
import textwrap
import unittest
from unittest.mock import Mock, patch

import appliance_cli as module


ALLOWED_COMMANDS = {
    "ping", "tcpdump", "traceroute", "ifconfig", "iptables",
    "dmesg", "ip", "dig", "htop", "top",
}


def make_cli():
    cli = module.AellaCli.__new__(module.AellaCli)
    cmd.Cmd.__init__(cli, stdin=io.StringIO(), stdout=io.StringIO())
    cli.shell_command = sorted(ALLOWED_COMMANDS)
    return cli


class DiagnosticCommandPolicyTests(unittest.TestCase):
    def setUp(self):
        self.cli = make_cli()

    def test_allowlist_contains_only_expected_diagnostics(self):
        self.assertEqual(set(self.cli.shell_command), ALLOWED_COMMANDS)

    def test_production_constructor_uses_exact_allowlist(self):
        source = textwrap.dedent(inspect.getsource(module.AellaCli.__init__))
        tree = ast.parse(source)
        actual = None
        for node in ast.walk(tree):
            if isinstance(node, ast.Assign) and any(
                isinstance(target, ast.Attribute) and target.attr == "shell_command"
                for target in node.targets
            ):
                actual = ast.literal_eval(node.value)
                break
        self.assertIsNotNone(actual)
        self.assertEqual(set(actual), ALLOWED_COMMANDS)

    def test_appliance_cli_contains_no_shell_execution_primitives(self):
        source = inspect.getsource(module.AellaCli)
        self.assertNotIn("shell=True", source)
        self.assertNotIn("os.system(", source)
        self.assertNotIn("os.popen(", source)

    def test_bang_is_parsed_as_separate_command(self):
        command, args, original = self.cli.parseline("!ip -br addr")
        self.assertEqual(command, "bang")
        self.assertEqual(args, "ip -br addr")
        self.assertEqual(original, "!ip -br addr")

    def test_allowed_ip_diagnostic_runs_without_shell(self):
        self.cli._resolve_shell_command = Mock(return_value="/usr/sbin/ip")
        with patch.object(module.subprocess, "call", return_value=0) as run:
            self.cli.onecmd("!ip -br addr")
        run.assert_called_once()
        argv = run.call_args.args[0]
        self.assertEqual(argv, ["/usr/sbin/ip", "-br", "addr"])
        self.assertIs(run.call_args.kwargs["shell"], False)

    def test_user_scoped_diagnostic_runs_as_invoking_user(self):
        self.cli._resolve_shell_command = Mock(return_value="/usr/bin/ping")
        with patch.object(module, "_get_invoking_username", return_value="stellar"):
            with patch.object(module.subprocess, "call", return_value=0) as run:
                self.cli.onecmd("!ping -c 1 127.0.0.1")
        argv = run.call_args.args[0]
        self.assertEqual(
            argv,
            ["/usr/bin/sudo", "-u", "stellar", "--", "/usr/bin/ping", "-c", "1", "127.0.0.1"],
        )
        self.assertIs(run.call_args.kwargs["shell"], False)

    def test_unknown_command_is_blocked(self):
        with patch.object(module.subprocess, "call") as run:
            self.cli.onecmd("!bash -c id")
        run.assert_not_called()

    def test_ip_netns_exec_is_blocked(self):
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ip", "netns", "exec", "test", "/bin/bash"]))
        with patch.object(module.subprocess, "call") as run:
            self.cli.onecmd("!ip netns exec test /bin/bash")
        run.assert_not_called()

    def test_ip_mutating_commands_are_blocked(self):
        for args in (
            ["ip", "link", "set", "eth0", "down"],
            ["ip", "route", "add", "default", "via", "192.0.2.1"],
            ["ip", "netns", "add", "test"],
        ):
            with self.subTest(args=args):
                self.assertFalse(self.cli._is_safe_shell_diagnostic(args))

    def test_tcpdump_file_and_postrotate_execution_are_blocked(self):
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["tcpdump", "-w", "/tmp/capture.pcap"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["tcpdump", "-z", "/bin/sh"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["tcpdump", "--postrotate-command", "/bin/sh"]))

    def test_iptables_mutations_are_blocked(self):
        for args in (
            ["iptables", "-F"],
            ["iptables", "-A", "INPUT", "-j", "ACCEPT"],
            ["iptables", "-D", "INPUT", "1"],
            ["iptables", "-L", "-Z"],
        ):
            with self.subTest(args=args):
                self.assertFalse(self.cli._is_safe_shell_diagnostic(args))

    def test_dmesg_mutations_are_blocked(self):
        for args in (["dmesg", "-C"], ["dmesg", "--clear"], ["dmesg", "-n", "1"], ["dmesg", "-D"]):
            with self.subTest(args=args):
                self.assertFalse(self.cli._is_safe_shell_diagnostic(args))

    def test_ifconfig_mutations_are_blocked(self):
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["ifconfig", "mgt"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ifconfig", "mgt", "down"]))

    def test_ping_flood_and_unbounded_preload_are_blocked(self):
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ping", "-f", "127.0.0.1"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ping", "-l", "100000", "127.0.0.1"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["ping", "-c", "1000", "127.0.0.1"]))
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["ping", "-c", "4", "127.0.0.1"]))

    def test_top_is_forced_to_bounded_batch_mode(self):
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["top"]))
        self.assertTrue(self.cli._is_safe_shell_diagnostic(["top", "-d", "1"]))
        self.assertFalse(self.cli._is_safe_shell_diagnostic(["top", "-b", "-n", "1000"]))
        self.cli._resolve_shell_command = Mock(return_value="/usr/bin/top")
        with patch.object(module, "_get_invoking_username", return_value="stellar"):
            with patch.object(module.subprocess, "call", return_value=0) as run:
                self.cli.onecmd("!top")
        argv = run.call_args.args[0]
        self.assertEqual(argv[-3:], ["-b", "-n", "1"])
        self.assertIs(run.call_args.kwargs["shell"], False)

    def test_binary_resolution_requires_trusted_root_owned_system_path(self):
        self.cli._resolve_shell_command = module.AellaCli._resolve_shell_command.__get__(self.cli)
        with patch.object(module.shutil, "which", return_value="/tmp/evil/ip"):
            self.assertIsNone(self.cli._resolve_shell_command("ip"))


class ShellAccessTests(unittest.TestCase):
    def setUp(self):
        self.cli = make_cli()

    def test_shell_rejects_arguments_before_password_prompt(self):
        self.cli.is_password_valid = Mock(return_value=True)
        with patch.object(module.subprocess, "call") as run:
            self.cli.do_shell("ip addr")
        self.cli.is_password_valid.assert_not_called()
        run.assert_not_called()

    def test_shell_requires_account_password(self):
        self.cli.is_password_valid = Mock(return_value=False)
        with patch.object(module.subprocess, "call") as run:
            self.cli.do_shell("")
        self.cli.is_password_valid.assert_called_once()
        run.assert_not_called()

    def test_shell_opens_only_login_bash_after_authentication(self):
        self.cli.is_password_valid = Mock(return_value=True)
        with patch.object(module.subprocess, "call", return_value=0) as run:
            self.cli.do_shell("")
        run.assert_called_once_with(["/bin/bash", "--login"], cwd="/root", shell=False)


class InternalCommandSafetyTests(unittest.TestCase):
    def setUp(self):
        self.cli = make_cli()

    def test_internal_command_runner_never_uses_shell(self):
        with patch.object(module.subprocess, "run", return_value=Mock(returncode=0, stdout=b"host\n", stderr=b"")) as run:
            self.cli.shell_cmd_exec("hostname")
        self.assertEqual(run.call_args.args[0], ["hostname"])
        self.assertNotIn("shell", run.call_args.kwargs)

    def test_run_command_with_stderr_rejects_command_strings(self):
        ok, message = self.cli.run_command_with_stderr("id")
        self.assertFalse(ok)
        self.assertIn("argv", message)

    def test_acl_comment_is_passed_as_one_literal_argv_value(self):
        args = self.cli._build_user_rule_args(
            "data1g", "192.0.2.10", "allow", "198.51.100.0/24",
            "443", "test $(id); " + chr(96) + "id" + chr(96),
        )
        comment_index = args.index("--comment")
        comment = args[comment_index + 1]
        self.assertIn("$(id)", comment)
        self.assertIn(chr(96) + "id" + chr(96), comment)
        self.assertEqual(args[-1], comment)

    def test_acl_command_runner_does_not_expand_shell_metacharacters(self):
        with patch.object(module.subprocess, "run", return_value=Mock(returncode=0, stdout="", stderr="")) as run:
            command = 'sudo iptables -A TEST -m comment --comment "literal $(id); ' + chr(96) + 'id' + chr(96) + '" -j ACCEPT'
            self.cli._run_cmd(command)
        self.assertNotIn("shell", run.call_args.kwargs)
        self.assertIn("literal $(id); " + chr(96) + "id" + chr(96), run.call_args.args[0])

    def test_acl_staging_uses_atomic_root_owned_state_not_tmp(self):
        source = inspect.getsource(module.AellaCli._save_acl_staging)
        self.assertIn("_write_root_text_file", source)
        self.assertNotIn("/tmp/", source)

    def test_clear_cli_history_does_not_use_shell_or_os_system(self):
        source = inspect.getsource(module.AellaCli.clear_cli_callback)
        self.assertNotIn("os.system", source)
        self.assertNotIn("shell=True", source)
        self.assertIn("Path(LOG_DIR)", source)

    def test_log_and_patch_storage_are_outside_user_home(self):
        self.assertEqual(module.PATCH_DIR, "/var/lib/aella/hotfix")
        self.assertNotIn("/home/stellar", module.PATCH_DIR)
        source = inspect.getsource(module.RotatingFileHandler.__init__)
        self.assertIn("_ensure_root_owned_directory", source)

    def test_direct_apt_package_install_is_disabled(self):
        with patch.object(self.cli, "run_command_with_stderr") as run:
            self.cli.set_patches_callback("patches", ["bash"])
        run.assert_not_called()

    def test_patch_name_path_traversal_is_rejected(self):
        with patch.object(module, "_ensure_patch_storage") as ensure:
            self.cli.set_patches_callback("patches", ["apply", "../../etc/passwd"])
        ensure.assert_not_called()

    def test_hostname_shell_metacharacters_are_rejected(self):
        with patch.object(module.subprocess, "run") as run:
            self.cli.set_hostname_callback("hostname", ["bad$(id)"])
        run.assert_not_called()


if __name__ == "__main__":
    unittest.main()
