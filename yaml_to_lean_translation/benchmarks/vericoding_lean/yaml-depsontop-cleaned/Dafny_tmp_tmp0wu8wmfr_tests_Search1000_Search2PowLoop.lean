import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search2PowLoop",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search2PowLoop",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Is2Pow(n) is true iff n==2^k for some k>=0.
Translated from Dafny predicate.
-/
def Is2Pow (n : Int) : Bool :=
  if n < 1 then
    false
  else if n == 1 then 
    true
  else
    n % 2 == 0 ∧ Is2Pow (n/2)

/--
Search2PowLoop performs binary search on a sorted array segment.
Only works for array segments of size n == 2^k-1 for some k>=0.
Translated from Dafny method.
-/
def Search2PowLoop (a : Array Int) (i : Int) (n : Int) (x : Int) : Int :=
  sorry

/--
Specification for Search2PowLoop.
Translated from Dafny requires/ensures.
-/
theorem Search2PowLoop_spec 
  (a : Array Int) (i : Int) (n : Int) (x : Int) :
  (0 ≤ i) →
  (i + n ≤ a.size) →
  (∀ p q, i ≤ p → p < q → q < i + n → a.get ⟨p⟩ ≤ a.get ⟨q⟩) →
  Is2Pow (n + 1) →
  let k := Search2PowLoop a i n x
  i ≤ k ∧ k ≤ i + n ∧
  (∀ r, i ≤ r → r < k → a.get ⟨r⟩ < x) ∧
  (∀ r, k ≤ r → r < i + n → a.get ⟨r⟩ ≥ x) := sorry

end DafnyBenchmarks