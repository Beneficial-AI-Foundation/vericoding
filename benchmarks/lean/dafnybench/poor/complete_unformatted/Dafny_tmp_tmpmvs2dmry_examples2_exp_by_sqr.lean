import Std

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmpmvs2dmry_examples2_exp_by_sqr",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmpmvs2dmry_examples2_exp_by_sqr",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/-- Translation of Dafny gcd function -/
partial def gcd (m n : Nat) : Nat :=
  if m = n then n
  else if m > n then gcd (m - n) n
  else gcd m (n - m)

/-- Specification for gcd function -/
theorem gcd_spec (m n : Nat) :
  m > 0 ∧ n > 0 → gcd m n > 0 := sorry

/-- Translation of Dafny exp function -/
def exp (x : Float) (n : Nat) : Float :=
  if n = 0 then 1.0
  else if x == 0.0 then 0.0
  else if n = 0 ∧ x == 0.0 then 1.0
  else x * exp x (n - 1)

/-- Translation of Dafny exp_by_sqr method -/
def exp_by_sqr (x0 : Float) (n0 : Nat) : Float := sorry

/-- Specification for exp_by_sqr method -/
theorem exp_by_sqr_spec (x0 : Float) (n0 : Nat) :
  x0 ≥ 0.0 → exp_by_sqr x0 n0 = exp x0 n0 := sorry

end DafnyBenchmarks
