```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim_gcdI",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Programmverifikation-und-synthese_tmp_tmppurk6ime_PVS_Assignment_ex_06_Hoangkim_ex_06_hoangkim_gcdI",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["gcd", "gcd'"],
  "methods": ["gcdI"]
}
-/

namespace DafnyBenchmarks

/-- Translation of Dafny ghost function gcd -/
def gcd (x y : Int) : Int :=
  if x = y then x
  else if x > y then gcd (x - y) y 
  else gcd x (y - x)

/-- Specification for gcd function -/
theorem gcd_spec (x y : Int) :
  x > 0 ∧ y > 0 → gcd x y > 0 := sorry

/-- Translation of Dafny ghost function gcd' -/
def gcd' (x y : Int) : Int :=
  if x = y then x
  else if x > y then gcd' (x - y) y
  else gcd y x

/-- Specification for gcd' function -/
theorem gcd'_spec (x y : Int) :
  x > 0 ∧ y > 0 → gcd' x y > 0 := sorry

/-- Translation of Dafny method gcdI -/
def gcdI (m n : Int) : Int := sorry

/-- Specification for gcdI method -/
theorem gcdI_spec (m n : Int) :
  m > 0 ∧ n > 0 → gcdI m n = gcd m n := sorry

end DafnyBenchmarks
```