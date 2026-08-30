# Benchmark sets

A set file names the tasks a run covers. One glob per line, relative to
`benchmarks/`; `#` comments and blank lines ignored.

Both runners read these files, so a local run and a BenchExec run cover exactly
the same tasks. A result is only comparable to another result over the same set.

| set | tasks | purpose |
|---|---|---|
| `smoke.set` | ~140 | fast gate before scoring. Seconds, not minutes. |
| `ajave.set` | 71 | our own feature suite, JVM-verified ground truth |
| `concurrency.set` | 14 | the concurrency litmus tests |
| `sv-comp.set` | 1033 | the full official corpus — competition scoring |

Prefer adding a task to `benchmarks/ajave/` over adding to `smoke.set`: our own
tasks carry per-property ground truth verified against a real JVM, whereas
`smoke.set` borrows tasks from the corpus we also score on. `CLAUDE.md` keeps the
smoke suite under 80 entries for this reason.
