# Benchmarks

Everything ajave is measured against, and the two runners that measure it.

```
benchmarks/
  sv-comp/      the official SV-COMP Java corpus (1033 tasks) — gitignored,
                fetched separately; this is what the competition score means
  ajave/        our own suite (71 tasks) — per-property ground truth,
                verified against a real JVM
  sets/         named subsets both runners read
  benchexec/    tool-info module and benchmark definitions
```

## Running

`tools/bench.py` is the general-purpose runner.

```sh
tools/bench.py --set smoke                      # fast gate before scoring
tools/bench.py --set ajave --check              # our suite, fail on regression
tools/bench.py --set sv-comp --property valid-assert --by-category --timing
tools/bench.py --set ajave --update-baseline    # record current outcomes
```

Ground truth always comes from the task's own `.yml`. The runner never decides
what a task *should* answer — that is the invariant that keeps the gate honest,
and its absence is what allowed the property mismatch in #54.

### Outcomes

| outcome | meaning | fails `--check` |
|---|---|---|
| `correct` | matches the declared verdict | no |
| `unproven` | UNKNOWN, TIMEOUT or ERROR | only if it was `correct` in the baseline |
| `WRONG` | the opposite of the declared verdict | **always** |

A wrong TRUE costs −16 and a wrong FALSE −32, so one wrong answer erases eight
correct TRUEs. An UNKNOWN that was already UNKNOWN is not a regression —
precision we never had is not something we lost, and treating it as a failure is
what made the previous corpus suite noisy enough to ignore.

## Two runners, and why

| | `tools/bench.py` | BenchExec |
|---|---|---|
| platform | any | **Linux only** |
| resource limits | wall-clock timeout | CPU, memory, time via cgroups |
| use for | development, CI gating | competition-fidelity measurement |

BenchExec enforces limits through Linux cgroups, which do not exist on macOS, so
it cannot be the local loop on a Mac. Both read the same task files and the same
set files, so they agree on *what* is covered; only the resource enforcement
differs.

## Measurement hygiene

**Timeout counts are contention-sensitive.** The same build measured 89 timeouts
on a loaded machine and 43 on an idle one — a ~20 point swing that looked exactly
like a code regression and was investigated as one (#64).

`bench.py` checks load average before starting and warns; pass `--require-idle`
to make it refuse instead. Use that for any run whose numbers you intend to
compare against another run. Every report prints the machine state, so two
results are either comparable or visibly not.

## Cleanup

Every run kills its children as a **process group**, and sweeps on the way out.

This is not incidental. `subprocess.run(timeout=…)` and Rust's `Child::kill`
both signal only the direct child, but ajave spawns a solver (z3/cvc5) and a
real JVM for witness replay. Every timed-out task therefore leaked a solver and
a JVM, each holding hundreds of megabytes and running indefinitely. Across a
corpus run that compounded until the machine exhausted its memory and froze —
and while load was climbing toward 61 on a 10-core box, every timing measured
was quietly worthless.

Both runners now put each task in its own process group and kill the group, so
nothing can outlive the run that started it. `tools/procguard.py` implements it
for Python and has a test proving `subprocess.run` leaks where it does not.

After an interrupted run, or any time the machine feels slow:

```sh
tools/cleanup.sh          # kill strays, remove temp dirs
tools/cleanup.sh --dry    # report only
tools/bench.py --sweep …  # sweep before starting a run
```

`cleanup.sh` matches only patterns unique to this project — never a bare `java`
or `z3`, which would kill your own work.

`bench.py` also refuses to start more workers than the machine has memory for
(about 1.5GB per worker: one ajave, one solver, one JVM).

## Adding tasks

Prefer `benchmarks/ajave/` over adding to `smoke.set`. Our own tasks carry
ground truth established by construction and checked against a real JVM by
`tools/validate_own_benchmarks.py`, whereas the smoke set borrows tasks from the
corpus we also score on — tuning against those is measuring yourself with your
own ruler (see the overfitting section of `CLAUDE.md`).

Every wrong-answer fix must add a canary; that rule is in `CLAUDE.md` and is not
optional.
