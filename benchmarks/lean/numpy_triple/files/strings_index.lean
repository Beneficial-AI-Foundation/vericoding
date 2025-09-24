-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def index {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem index_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 
      -- Valid range bounds
      0 ≤ start.get i ∧ start.get i ≤ endPos.get i ∧
      endPos.get i ≤ (a.get i).length ∧
      -- Substring must exist in each string within the range
      ∃ j : Nat, (start.get i).toNat ≤ j ∧ 
        j + (sub.get i).length ≤ min (endPos.get i + 1).toNat (a.get i).length ∧
        ((a.get i).drop j).take (sub.get i).length = sub.get i⌝⦄
    index a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Result is always non-negative (no -1 values like find)
      result.get i ≥ 0 ∧
      -- Result is within the valid search range
      start.get i ≤ result.get i ∧ 
      result.get i ≤ endPos.get i ∧
      -- The substring is found at the returned index
      Int.natAbs (result.get i) + (sub.get i).length ≤ (a.get i).length ∧
      ((a.get i).drop (Int.natAbs (result.get i))).take (sub.get i).length = sub.get i ∧
      -- This is the lowest (leftmost) index where substring is found in the range
      (∀ j : Nat, (start.get i).toNat ≤ j ∧ j < Int.natAbs (result.get i) → 
        ¬(((a.get i).drop j).take (sub.get i).length = sub.get i))⌝⦄ := by
  sorry
-- </vc-theorems>