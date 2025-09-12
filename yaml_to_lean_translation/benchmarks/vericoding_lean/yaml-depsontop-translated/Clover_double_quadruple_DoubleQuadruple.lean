```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Clover_double_quadruple_DoubleQuadruple",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_double_quadruple_DoubleQuadruple",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["DoubleQuadruple"]
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny method DoubleQuadruple which returns two values:
- a: double of input x
- b: quadruple of input x

Original ensures clauses:
- a == 2 * x
- b == 4 * x
-/
def DoubleQuadruple (x : Int) : Int × Int := sorry

/--
Specification for DoubleQuadruple method ensuring:
1. First return value is double the input
2. Second return value is quadruple the input
-/
theorem DoubleQuadruple_spec (x : Int) :
  let (a, b) := DoubleQuadruple x
  a = 2 * x ∧ b = 4 * x := sorry

end DafnyBenchmarks
```