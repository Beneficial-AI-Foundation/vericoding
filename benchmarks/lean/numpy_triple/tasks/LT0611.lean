-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ endPos.get i ∧ endPos.get i < (a.get i).length⌝⦄
    find a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Case 1: substring not found (returns -1)
      (result.get i = -1 ↔ 
        ∀ pos : Nat, start.get i ≤ pos ∧ pos ≤ endPos.get i ∧ pos + (sub.get i).length ≤ (a.get i).length → 
          ¬(((a.get i).drop pos).take (sub.get i).length = sub.get i)) ∧
      -- Case 2: substring found (returns non-negative index)
      (result.get i ≥ 0 → 
        -- Result is within valid range
        start.get i ≤ result.get i ∧ 
        result.get i ≤ endPos.get i ∧
        result.get i + (sub.get i).length ≤ (a.get i).length ∧
        -- Substring actually found at this position
        ((a.get i).drop (Int.natAbs (result.get i))).take (sub.get i).length = sub.get i ∧
        -- This is the LOWEST index where substring is found (minimality property)
        (∀ pos : Nat, start.get i ≤ pos ∧ pos < Int.natAbs (result.get i) → 
          ¬(((a.get i).drop pos).take (sub.get i).length = sub.get i))) ∧
      -- Sanity check 1: empty substring is found at start position
      (sub.get i = "" → result.get i = start.get i) ∧
      -- Sanity check 2: substring longer than remaining string cannot be found
      (start.get i + (sub.get i).length > (a.get i).length → result.get i = -1) ∧
      -- Sanity check 3: if start > end, no substring can be found
      (start.get i > endPos.get i → result.get i = -1)⌝⦄ := by
  sorry
-- </vc-theorems>