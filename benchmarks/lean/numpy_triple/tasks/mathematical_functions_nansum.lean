-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nansum {n : Nat} (a : Vector Float n) : Id Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nansum_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nansum a
    ⦃⇓result => ⌜
      -- Core property: result equals sum of non-NaN elements
      result = (List.range n).foldl (fun acc i => 
        let val := a.get ⟨i, by sorry⟩
        if val.isNaN then acc else acc + val) 0 ∧
      -- If all elements are NaN, result is 0 (numpy >= 1.9.0 behavior)
      (∀ i : Fin n, (a.get i).isNaN → result = 0) ∧
      -- NaN values contribute 0 to the sum
      (∀ i : Fin n, (a.get i).isNaN → 
        ∃ s : Float, s = (List.range n).foldl (fun acc j => 
          if j = i.val then acc + 0 else 
          let val := a.get ⟨j, by sorry⟩
          if val.isNaN then acc else acc + val) 0 ∧ result = s) ∧
      -- Handling infinities: if both +inf and -inf present, result is NaN
      ((∃ i : Fin n, ¬(a.get i).isFinite ∧ a.get i > 0) ∧ 
       (∃ j : Fin n, ¬(a.get j).isFinite ∧ a.get j < 0) → 
        result.isNaN) ∧
      -- If only positive infinity present, result is positive infinity
      ((∃ i : Fin n, ¬(a.get i).isFinite ∧ a.get i > 0) ∧ 
       (∀ j : Fin n, ¬(¬(a.get j).isFinite ∧ a.get j < 0)) → 
        ¬result.isFinite ∧ result > 0) ∧
      -- If only negative infinity present, result is negative infinity
      ((∃ i : Fin n, ¬(a.get i).isFinite ∧ a.get i < 0) ∧ 
       (∀ j : Fin n, ¬(¬(a.get j).isFinite ∧ a.get j > 0)) → 
        ¬result.isFinite ∧ result < 0) ∧
      -- If vector is empty, result is 0
      (n = 0 → result = 0)
    ⌝⦄ := by
  sorry
-- </vc-theorems>