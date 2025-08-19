import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "NPY_LOG10E",
  "category": "C API Mathematical constants",
  "description": "Base 10 logarithm of e",
  "doc": "log10(e) = 0.434294481903251827651128918916605082",
  "code": "#define NPY_LOG10E 0.434294481903251827651128918916605082"
}
-/

open Std.Do

/-- Base 10 logarithm of Euler's number e -/
def nPY_LOG10E : Id Float :=
  pure 0.434294481903251827651128918916605082

/-- Specification: nPY_LOG10E returns the base 10 logarithm of e with correct mathematical properties -/
theorem nPY_LOG10E_spec :
    ⦃⌜True⌝⦄
    nPY_LOG10E
    ⦃⇓result => ⌜
      -- The value should be log₁₀(e)
      result = 0.434294481903251827651128918916605082 ∧
      -- Mathematical property: 10^result = e (within floating-point precision)
      Float.abs (10.0 ^ result - Float.exp 1.0) < 1e-15 ∧
      -- Another mathematical property: result * ln(10) = 1 (since log₁₀(e) * ln(10) = ln(e) = 1)
      Float.abs (result * Float.log 10.0 - 1.0) < 1e-15 ∧
      -- The value is positive (since e > 1 and log₁₀ is increasing)
      result > 0.0 ∧
      -- The value is less than 1 (since e < 10)
      result < 1.0
    ⌝⦄ := by
  simp [nPY_LOG10E]
  apply triple_pure
  simp
  constructor
  · rfl
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num