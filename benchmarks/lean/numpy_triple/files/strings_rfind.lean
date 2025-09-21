-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rfind {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rfind_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ endPos.get i⌝⦄
    rfind a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Basic range constraint: result is -1 or within string bounds
      (result.get i = -1 ∨ (0 ≤ result.get i ∧ result.get i < (a.get i).length)) ∧
      -- If result is -1, no occurrence of substring within the specified range
      (result.get i = -1 → 
        ∀ j : Nat, start.get i ≤ j ∧ j + (sub.get i).length ≤ Int.natAbs (endPos.get i) + 1 ∧ 
                   j + (sub.get i).length ≤ (a.get i).length → 
          ¬String.startsWith ((a.get i).drop j) (sub.get i)) ∧
      -- If result is non-negative, it's the rightmost valid occurrence
      (result.get i ≥ 0 → 
        -- The result is within the search range
        start.get i ≤ result.get i ∧ 
        result.get i + (sub.get i).length ≤ endPos.get i + 1 ∧
        -- The substring matches at this position
        String.startsWith ((a.get i).drop (Int.natAbs (result.get i))) (sub.get i) ∧
        -- This is the rightmost occurrence within the range
        (∀ j : Int, result.get i < j ∧ j + (sub.get i).length ≤ endPos.get i + 1 ∧ 
                    start.get i ≤ j ∧ j + (sub.get i).length ≤ (a.get i).length → 
          ¬String.startsWith ((a.get i).drop (Int.natAbs j)) (sub.get i)))⌝⦄ := by
  sorry
-- </vc-theorems>