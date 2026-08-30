# NumPySimple — SPARK

26 tasks, each a translation of the same-named Dafny task in
`benchmarks/dafny/numpy_simple`. The Dafny specification is the authority;
the translation discipline, the two uniform language adaptations (bounded
integers, explicit division semantics) and the reasons the remaining 32
tasks were skipped are all in `../README.md`.

| | |
|---|---|
| tasks | 26 |
| reference solutions discharging at `--level=2` | 26 / 26 |
| proof obligations across the set | 387 (28 flow, 359 prover) |
| unproved | 0 |
| justified | 0 |

Element-wise: `NpAbs` `NpAdd` `NpSubtract` `NpMultiply` `NpSquare` `NpSign`
`NpClip` `NpCopy` `NpWhere` `NpZeros` `NpIsclose`

Comparisons: `NpEqual` `NpNotEqual` `NpGreater` `NpGreaterEqual` `NpLess`
`NpLessEqual`

Bitwise (32-bit modular words): `NpBitwiseAnd` `NpBitwiseOr` `NpBitwiseXor`

Division: `NpFloorDivide` `NpMod`

Reduction and scan: `NpMax` `NpMin` `NpArgmax` `NpCumSum`
