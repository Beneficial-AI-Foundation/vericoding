import Std

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search1000",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmp0wu8wmfr_tests_Search1000_Search1000",
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
partial def Is2Pow (n : Int) : Bool :=
  if n < 1 then
    false
  else if n == 1 then
    true
  else
    n % 2 == 0 ∧ Is2Pow (n/2)

/--
Binary search implementation that works for array segments of size n == 2^k-1.
Translated from Dafny method Search1000.
-/
def Search1000 (a : Array Int) (x : Int) : Int := sorry

/--
Specification for Search1000 method.
Translated from Dafny requires/ensures clauses.
-/
theorem Search1000_spec (a : Array Int) (x : Int) (k : Int) :
  a.size ≥ 1000 ∧
  (∀ p q, 0 ≤ p ∧ p < q ∧ q < 1000 → a[p]! ≤ a[q]!) →
  (0 ≤ k ∧ k ≤ 1000) ∧
  (∀ r, 0 ≤ r ∧ r < k → a[r.toNat]! < x) ∧
  (∀ r, k ≤ r ∧ r < 1000 → a[r.toNat]! ≥ x) := sorry

end DafnyBenchmarks
