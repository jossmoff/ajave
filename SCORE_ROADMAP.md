# Score Roadmap — SV-COMP valid-assert

Current: **554** (121 cT, 344 cF, 2 wT, 0 wF, 464 UNK, 82 TO)
Max possible: **1326** (313×2 TRUE + 700×1 FALSE)
Scoring: correct TRUE = +2, correct FALSE = +1, wrong TRUE = -16, wrong FALSE = -32

## UNKNOWN/TIMEOUT Breakdown (546 tasks)

| Category | UNK TRUE | UNK FALSE | Max pts | Key Blocker |
|----------|----------|-----------|---------|-------------|
| securibench | 19 | 67 | +105 | Heap aliasing, collections, inter-procedural |
| autostub (toString/string) | 0 | 35 | +35 | Integer.toString encoding in SMT string theory |
| autostub (float/double) | 0 | 48 | +48 | Float/double FP bit ops + casts |
| autostub (Unicode tables) | 0 | 24 | +24 | isDefined, isMirrored, getType, etc. (lookup tables) |
| autostub (misc int) | 1 | 5 | +7 | bitCount, highestOneBit(long), getInteger |
| autostub (String methods) | 0 | 24 | +24 | compareTo, indexOf variants, replace, trim |
| coral (NRA) | 0 | 62 | +62 | CVC5 transcendental solving |
| jbmc-string | 18 | 21 | +57 | StringBuilder ops, StringValue, SubString |
| float_unboundedloop | 29 | 0 | +58 | Float loop invariants |
| algorithms | 11 | 24 | +46 | Deep loops, heap structures |
| java-ranger | 9 | 14 | +32 | Deep call chains, method summaries |
| objects | 4 | 8 | +16 | Object identity, aliasing |
| recursive | 13 | 5 | +31 | Recursive method support |
| MinePump | 8 | 4 | +20 | Loop-heavy state machines |
| jpf (float casts) | 7 | 3 | +17 | f2i, d2l, i2d, fneg TRUE encoding |
| CWE | 3 | 6 | +12 | Float + readline modeling |
| misc/app | 14 | 9 | +37 | Various (list, enum, sync, instanceof) |
| jbmc misc | 16 | 15 | +47 | Cast, char, float, arrays, exceptions |
| **Wrong answers (2)** | — | — | **+34** | Refl4, StringValueOf07 |
| **TOTAL** | **152** | **374** | **~672** | — |

## Priority Tiers

### Tier 0: Fix Wrong Answers (+34)
- **Refl4**: TRUE→FALSE. Obligation not seeded in mock/library class bodies.
- **StringValueOf07**: TRUE→FALSE. Investigate unsound string discharge.

### Tier 1: Quick BV models (+7, LOW effort)
- `Integer.bitCount(int)`, `Long.bitCount(long)` — popcount BV encoding
- `Long.highestOneBit(long)` — same pattern as Integer version
- Already have the infrastructure; just add arms to `encode_math_call`.

### Tier 2: ToString string encoding (+35, MEDIUM effort)
- 35 autostub benchmarks need `Integer.toString(int)`, `Long.toString(long)`, `Short.toString`, `Byte.toString`, `Character.toString(char)` returning Z3 strings
- Partially done (Boolean/Integer/Short/Byte toString works for some); remaining need `toString(int,radix)`, `toHexString`, `toBinaryString`, `toOctalString`, `toUnsignedString`
- Radix conversions: encode as `str.from_int` for base-10, custom for hex/octal/binary

### Tier 3: Securibench heap + collections (+105, HIGH effort)
Largest single category. Sub-problems:
- **Collections modeling** (14 tasks): ArrayList/HashMap as array-backed models
- **Inter-procedural taint** (14 tasks): deeper inlining or method summaries
- **Aliasing** (5 tasks): must-alias tracking through field stores
- **Strong updates** (5 tasks): field-sensitive updates for single-object refs
- **Reflection** (4 tasks): Class.forName patterns
- **Session/Sanitizers** (9 tasks): string sanitization tracking
- **Remaining Basic/Pred/Factories** (35 tasks): mixed — many need collection+string flow

### Tier 4: String methods (+81, MEDIUM-HIGH effort)
- **jbmc-string** (39 tasks): StringBuilder append/insert/delete, StringConstructors, StringCompare, SubString, StringValueOf, StringMiscellaneous
- **autostub String** (24 tasks): compareTo, indexOf variants, lastIndexOf, replace, trim, toLowerCase, toUpperCase, regionMatches
- **Other string** (18 tasks): startswith, URLDecoder, LoopCharAt, etc.
- All route through Z3 QF_S string theory — extend existing `str_vars`/`field_str` infrastructure

### Tier 5: Float/Double support (+113, HIGH effort)
- **autostub float** (32 tasks): floatToRawIntBits, doubleToRawLongBits, isNaN, isInfinite, compare, byteValue/shortValue/intValue casts
- **jpf float casts** (10 tasks): f2i, d2l, i2d, i2f TRUE variants need float→int semantics
- **coral NRA** (62 tasks): CVC5 transcendental timeout; may need encoding improvements
- **CWE float** (9 tasks): float divide-by-zero with network input

### Tier 6: Hard problems (+168, VERY HIGH effort)
- **float_unboundedloop** (29 tasks): float loop invariants, need AI/widening
- **algorithms** (35 tasks): BellmanFord, MergeSort, RedBlackTree — deep loops + heap
- **recursive** (18 tasks): jayhorn-recursive, need summaries or bounded recursion
- **java-ranger** (23 tasks): deep program analysis
- **Unicode tables** (24 tasks): lookup table encoding for isDefined, getType, etc.

## Execution Plan

| Sprint | What | Points | Cumulative |
|--------|------|--------|------------|
| 1 | Fix 2 wrong answers + bitCount/highestOneBit | +41 | 595 |
| 2 | Autostub toString (radix, hex, octal) | +35 | 630 |
| 3 | String methods (QF_S extension) | +81 | 711 |
| 4 | Float/double BV models (FP bit ops, casts) | +50 | 761 |
| 5 | Securibench (collections, aliasing, inter-proc) | +60 | 821 |
| 6 | NRA/coral + float_unboundedloop | +50 | 871 |
| 7 | Recursive + algorithms + java-ranger | +40 | 911 |
