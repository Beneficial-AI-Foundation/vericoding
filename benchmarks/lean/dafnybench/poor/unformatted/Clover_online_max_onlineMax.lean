import Std


open Std.Do

/-!
{
  "name": "Clover_online_max_onlineMax",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_online_max_onlineMax",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny onlineMax method which finds the maximum value in an array
starting from index x. Returns the maximum value m and position p.

@param a The input array
@param x The starting index
@return (m, p) where m is the maximum value and p is its position
-/
def onlineMax (a : Array Int) (x : Int) : Int × Int := sorry

/--
Specification for onlineMax method translated from Dafny.
-/
theorem onlineMax_spec (a : Array Int) (x : Int) (m p : Int) :
  (1 ≤ x ∧ x < a.size) →
  (a.size ≠ 0) →
  let (m, p) := onlineMax a x;
  (x ≤ p ∧ p < a.size) ∧
  (∀ i, 0 ≤ i ∧ i < x → a[i.toNat]! ≤ m) ∧
  (∃ i, 0 ≤ i ∧ i < x ∧ a[i.toNat]! = m) ∧
  (x ≤ p ∧ p < a.size - 1 → (∀ i, 0 ≤ i ∧ i < p → a[i.toNat]! < a[p.toNat]!)) ∧
  ((∀ i, x ≤ i ∧ i < a.size ∧ a[i.toNat]! ≤ m) → p = a.size - 1) := sorry

end DafnyBenchmarks
