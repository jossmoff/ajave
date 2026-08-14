# Roadmap: 620 → 900

Current: **620** (131 cT, 374 cF, 1 wT (Refl4), 0 wF)
Target: **900** — gap: **280 points**

## Completed

### Encoding barrier lift (+29, 591 → 620)
- Removed `body_uses_havoced_ops` guard from k-induction, CHC, IMC
- Fixed BV width bug in `smt_encode.rs` (heap ops always 32-bit → descriptor-parsed)
- Fixed CHC apostrophe bug (Z3 HORN parser rejects `'` in identifiers)
- Added `bv_fresh` declarations to CHC encoding
- CEGAR guard kept (predicate abstraction unsound with havoced ops)
- K-induction now proves 8 new benchmarks (BellmanFord, InsertionSort, RedBlackTree, array/list/enum)

### Phase 3a: Float/Double bit-level operations (+11, 580 → 591)
- IEEE 754 Float/Double method encoding (18+ methods: floatToRawIntBits, isNaN, compare, etc.)
- CmpKind in IR (Long vs FloatL/FloatG) with BV totalOrder comparison
- BV const width bug fix (non-nibble-aligned widths → binary literals)
- JVM replay float/double bit-pattern reinterpretation
- Character toUpperCase/toLowerCase/toTitleCase soundness fix (fresh_bv)
- Boolean.hashCode encoding

### Phase 2a: String theory core (+6, 554 → 560)
Implemented 20+ String/StringBuilder methods in QF_S encoding (`str_encode.rs`):
- length, isEmpty, contains, equals, startsWith, endsWith, charAt, indexOf,
  lastIndexOf, substring, concat, toString, equalsIgnoreCase, regionMatches,
  replace, trim, toLowerCase, toUpperCase, hashCode, valueOf
- StringBuilder lifecycle: `<init>`, append, setLength, deleteCharAt, delete,
  insert, reverse with SSA alias propagation
- compareTo/compareToIgnoreCase REMOVED from encoding (Over-discharge unsoundness)
- Net +6 due to conservative encoding; many string benchmarks still UNKNOWN
  (solver timeouts on case-insensitive ops with 52 str.replace_all terms)

### Phase 1: Wrong-answer fixes (+20, 560 → 580)
- **Refl4** (wrong TRUE→UNKNOWN, +16): Vacuous TRUE guard — track `total_assertions`
  in Blackboard; if program has assertions but none reachable, return UNKNOWN.
- **StringValueOf07** (wrong TRUE→correct FALSE, +17): `signed_bv_to_str` was BV32-only;
  `valueOf(long)` passed BV64 causing Z3 sort mismatch → solver poisoning → unsound discharge.
  Fixed by parameterizing width. Also lost 5 vacuous TRUEs and 2 FALSEs from tighter guards.
- BV models (bitCount, highestOneBit, etc.) were already implemented.

## Phase 2b: String theory remaining (+40 → 620)

Revised down from +116 — core methods are done, remaining gains come from:

### Autostub toString variants (+15)
- `Integer.toString(int, int)` — radix conversion
- `Integer.toHexString/toBinaryString/toOctalString` — fixed-radix
- `Integer.toUnsignedString(int)` / `(int, int)`
- Same for Long variants (requires 64-bit str encoding)
- `Short.toString`, `Byte.toString` (static variants)
- `Character.toString(char)` (static)

### String constructors + remaining methods (+15)
- `new String(char[])`, `new String(byte[])` — array-to-string
- `compareTo` with bounded encoding (avoid Over discharge, Under only)
- `setCharAt` for StringBuilder
- `String.format` simple patterns (e.g. `%d`, `%s`)

### Solver robustness (+10)
- Case-insensitive operations cause Z3 Unknown (52 str.replace_all terms)
- Try CVC5 for string-heavy benchmarks (better QF_S support)
- Simplify toLowerCase/toUpperCase encoding (char-level vs string-level)

## Phase 3b: Float cast opcodes (+14 → 605)

### Float cast opcodes (jpf, 10 tasks) — 7 TRUE + 1 FALSE remaining
- `f2i`, `d2l`, `d2i`, `f2l` TRUE variants — need float arithmetic untainting or FP encoding
- `i2f`, `i2d` TRUE — int-to-float widening
- `fneg` TRUE — float negation
- Blocked by: float arithmetic taint (f+1.0 is tainted, casts inherit taint)
- Approach: either add FP theory, or untaint float-to-int casts and model conservatively

### Float/Double toString, intValue, etc. (autostub, ~14 tasks)
- `Float/Double.toString()` — needs float→string conversion in QF_S
- `Float/Double.intValue/longValue/byteValue/shortValue` — truncating casts (hard without FP theory)
- `Math.getExponent/round` — bit extraction / rounding

## Phase 4: Securibench (+60 → 730)

### Collection models
- `ArrayList` as `(array: Array BV32 BV32, size: BV32)` — `add`, `get`, `set`, `size`, `iterator`
- `HashMap` as `(keys: Array BV32 BV32, vals: Array BV32 BV32)` — `put`, `get`, `containsKey`
- `Iterator` — `hasNext`/`next` via index tracking

### Aliasing + strong updates
- Track must-alias sets: if ref `r` is the only ref to object `o`, field updates through `r` are strong updates
- Merge to weak updates when aliases exist

### Inter-procedural improvements
- Deeper inlining budget for securibench methods (many are shallow)
- Method summaries for simple getters/setters

## Phase 5: NRA + float loops (+50 → 780)

### NRA encoding improvements (62 coral tasks)
- Simplify ITE-heavy comparison encoding — direct inequality path conditions
- Better solver timeout tuning for CVC5 transcendental
- Try combining CVC5 NRA with dReal for different benchmark shapes

### Float loop invariants (29 float_unboundedloop tasks)
- Float-aware abstract interpretation (interval domain over FP)
- Or: encode as real-valued loops with FP rounding bounds

## Phase 6: Deep programs (+50 → 830)

### Recursive method support (18 tasks)
- Bounded recursion unrolling (depth 3-5)
- Or: recursive CHC encoding for Z3 fixedpoint

### Algorithm benchmarks (35 tasks)
- Better loop unrolling heuristics
- Heap-aware loop invariants for sorted structures

### java-ranger (23 tasks)
- Deeper call chain support
- Method summaries for repeated callees

## Phase 7: Stretch to 900 (+70 → 900)

### Deeper inlining + larger programs
- Increase inlining budget with lazy expansion
- Inter-procedural summaries for common library patterns

### Loop acceleration
- Pattern-match simple loops (counters, accumulators) to closed-form
- Bounded loop unrolling with widening

### Remaining categories
- Mop through remaining UNKNOWN verdicts category by category
- Targeted fixes for near-miss benchmarks

## Summary

| Phase | Technique | Points | Cumulative |
|-------|-----------|--------|------------|
| done | String theory core (2a) | +6 | 560 |
| done | Wrong-answer fixes (1) | +20 | 580 |
| done | Float/Double bit-level (3a) | +11 | 591 |
| done | Encoding barrier lift | +29 | 620 |
| 2b | String theory remaining | +30 | 650 |
| 3b | Float cast opcodes | +14 | 664 |
| 4 | Securibench (collections, aliasing) | +60 | 724 |
| 5 | NRA + float loops | +50 | 774 |
| 6 | Deep programs | +50 | 824 |
| 7 | Stretch (inlining, loops, mop-up) | +76 | 900 |

## ROI ranking
1. **Wrong answers** — highest per-benchmark ROI (34 pts for 2 fixes)
2. **String theory remaining** — infrastructure is built, incremental method additions
3. **Float/double** — broad impact across autostub + jpf + float benchmarks
4. **Securibench** — largest unsolved category, but needs heap + collections infra
5. **NRA/float loops** — moderate gains, hard solver problems
6. **Deep programs** — diminishing returns, hard verification
7. **Stretch** — everything else, incremental gains
