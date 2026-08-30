"""Run a subprocess so that killing it kills everything it started.

# Why this exists

`subprocess.run(..., timeout=N)` kills the process it spawned and nothing else.
ajave spawns grandchildren — `z3` or `cvc5` for solving, and a real `java` for
JVM witness replay — so a timeout left those orphaned and running. Every
timed-out task leaked a solver and a JVM, each holding hundreds of megabytes.

Across a corpus run with dozens of timeouts that compounded until the machine ran
out of memory and froze. Load average reached 61 on a 10-core box, which also
silently invalidated every timing measurement taken while it was climbing.

The fix is to give each child its own process group and kill the *group*, so no
descendant can outlive the run that started it.

# Usage

    from procguard import run_guarded
    result = run_guarded(cmd, timeout=60, env=env)
    result.verdict_stdout, result.stderr, result.timed_out

Cleanup is unconditional: it happens on timeout, on exception, and on
KeyboardInterrupt, because those are exactly the paths that leaked before.
"""

import os
import signal
import subprocess
import sys
import time
from dataclasses import dataclass

# Every process group this interpreter has started and not yet reaped. A signal
# handler walks this so Ctrl-C cleans up too — interrupting a run was one of the
# ways strays accumulated.
_LIVE_GROUPS = set()


@dataclass
class GuardedResult:
    stdout: str
    stderr: str
    returncode: int
    timed_out: bool
    elapsed: float


def _kill_group(pgid, grace=0.5):
    """SIGTERM the group, then SIGKILL whatever ignored it."""
    for sig in (signal.SIGTERM, signal.SIGKILL):
        try:
            os.killpg(pgid, sig)
        except (ProcessLookupError, PermissionError):
            return
        if sig is signal.SIGTERM:
            # Give the JVM a moment to exit cleanly so it removes its own temp
            # files; SIGKILL leaves them behind for the sweeper.
            deadline = time.time() + grace
            while time.time() < deadline:
                try:
                    os.killpg(pgid, 0)
                except (ProcessLookupError, PermissionError):
                    return
                time.sleep(0.05)


def _cleanup_all(signum=None, frame=None):
    for pgid in list(_LIVE_GROUPS):
        _kill_group(pgid, grace=0.1)
    _LIVE_GROUPS.clear()
    if signum is not None:
        # Restore default handling and re-raise so the caller still sees the
        # interrupt rather than a silently swallowed one.
        signal.signal(signum, signal.SIG_DFL)
        os.kill(os.getpid(), signum)


def install_signal_handlers():
    """Kill outstanding process groups on interrupt or termination."""
    for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
        try:
            signal.signal(sig, _cleanup_all)
        except (ValueError, OSError):
            # Not in the main thread, or the signal is unavailable here.
            pass


def run_guarded(cmd, timeout, env=None, cwd=None):
    """Run `cmd`, killing its whole process group if it overruns `timeout`."""
    start = time.time()
    try:
        proc = subprocess.Popen(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            env=env,
            cwd=cwd,
            # Detach into a new session, making the child a process-group
            # leader. Everything it spawns inherits that group, so one killpg
            # reaches the solver and the JVM as well.
            start_new_session=True,
        )
    except OSError as e:
        return GuardedResult("", f"spawn failed: {e}", -1, False, 0.0)

    try:
        pgid = os.getpgid(proc.pid)
    except ProcessLookupError:
        pgid = proc.pid
    _LIVE_GROUPS.add(pgid)

    timed_out = False
    try:
        stdout, stderr = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        timed_out = True
        _kill_group(pgid)
        try:
            stdout, stderr = proc.communicate(timeout=5)
        except subprocess.TimeoutExpired:
            stdout, stderr = "", ""
    except BaseException:
        # Includes KeyboardInterrupt. Never leave the group running.
        _kill_group(pgid)
        raise
    finally:
        # Belt and braces: even on the clean path a grandchild may have
        # outlived its parent, which is the leak this module exists to stop.
        _kill_group(pgid, grace=0.0)
        _LIVE_GROUPS.discard(pgid)

    return GuardedResult(
        stdout or "", stderr or "", proc.returncode or 0, timed_out,
        time.time() - start,
    )


# --------------------------------------------------------------------------
# Sweeper for strays left by earlier runs
# --------------------------------------------------------------------------

# Matched against the full command line. Deliberately specific: a bare "java"
# or "z3" would match the user's own work.
STRAY_PATTERNS = ["ajave-shadow", "ajave-build"]
STRAY_NAMES = ["ajave"]


def find_strays():
    """(pid, cmdline) for processes this project leaked."""
    try:
        out = subprocess.run(
            ["ps", "-eo", "pid=,command="], capture_output=True, text=True,
            timeout=10,
        ).stdout
    except (OSError, subprocess.SubprocessError):
        return []
    mine = os.getpid()
    strays = []
    for line in out.splitlines():
        line = line.strip()
        if not line:
            continue
        pid_s, _, cmd = line.partition(" ")
        try:
            pid = int(pid_s)
        except ValueError:
            continue
        if pid == mine:
            continue
        if any(p in cmd for p in STRAY_PATTERNS) or \
           any(cmd.split()[0].endswith("/" + n) for n in STRAY_NAMES if cmd.split()):
            strays.append((pid, cmd[:120]))
    return strays


def sweep(verbose=True):
    """Kill leftover processes and remove this project's temp directories."""
    killed = 0
    for pid, cmd in find_strays():
        try:
            os.kill(pid, signal.SIGKILL)
            killed += 1
            if verbose:
                print(f"  killed {pid}: {cmd}", file=sys.stderr)
        except (ProcessLookupError, PermissionError):
            pass

    removed = 0
    import glob
    import shutil
    import tempfile

    # Only the directories ajave actually creates for a run. A blanket
    # `ajave-*` glob is too wide: it also matched `/tmp/ajave-runs`, the
    # directory holding this harness's own logs, so a completed run deleted its
    # own results on the way out and took the chained run with it.
    prefixes = ("ajave-build-", "ajave-shadow-")
    roots = {tempfile.gettempdir(), "/tmp"}
    for root in roots:
        for prefix in prefixes:
            for d in glob.glob(os.path.join(root, prefix + "*")):
                try:
                    shutil.rmtree(d, ignore_errors=True)
                    removed += 1
                except OSError:
                    pass
    if verbose and (killed or removed):
        print(f"  swept {killed} process(es), {removed} temp dir(s)",
              file=sys.stderr)
    return killed, removed
