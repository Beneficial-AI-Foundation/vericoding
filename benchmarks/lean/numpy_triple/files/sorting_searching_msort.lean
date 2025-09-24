-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def msort {n : Nat} (a : Vector Float n) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem msort_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    msort a
    ⦃⇓result => ⌜
      -- The result is sorted in ascending order
      (∀ i j : Fin n, i.val < j.val → result.get i ≤ result.get j) ∧
      -- The result is a permutation of the input (same multiset of elements)
      (∀ x : Float, (a.toList.count x) = (result.toList.count x))
    ⌝⦄ := by
  sorry
-- </vc-theorems>