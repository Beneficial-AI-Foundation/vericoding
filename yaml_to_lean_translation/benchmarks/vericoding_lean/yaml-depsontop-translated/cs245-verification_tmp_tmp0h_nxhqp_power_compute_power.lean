```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "cs245-verification_tmp_tmp0h_nxhqp_power_compute_power",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: cs245-verification_tmp_tmp0h_nxhqp_power_compute_power", 
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["power"],
  "methods": ["compute_power"]
}
-/

namespace DafnyBenchmarks

/--
Power function that computes a^n.
Requires a ≥ 0 and n ≥ 0.
-/
def power (a n : Int) : Int :=
  if n = 0 then 1 else a * power a (n - 1)

/--
Specification for power function.
-/
theorem power_spec (a n : Int) :
  a ≥ 0 ∧ n ≥ 0 → power a n ≥ 0 := sorry

/--
Compute power method that returns a^n.
Requires a ≥ 0 and n ≥ 0.
Ensures result equals power(a,n).
-/
def compute_power (a n : Int) : Int := sorry

/--
Specification for compute_power method.
-/
theorem compute_power_spec (a n : Int) :
  a ≥ 0 ∧ n ≥ 0 → compute_power a n = power a n := sorry

end DafnyBenchmarks
```