-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n)
    (h_range : ∀ i : Fin n, start.get i ≤ endPos.get i) 
    (h_bounds_start : ∀ i : Fin n, 0 ≤ start.get i ∧ start.get i ≤ (a.get i).length) 
    (h_bounds_end : ∀ i : Fin n, 0 ≤ endPos.get i ∧ endPos.get i ≤ (a.get i).length) 
    (h_nonempty : ∀ i : Fin n, sub.get i ≠ "") :
    ⦃⌜∀ i : Fin n, start.get i ≤ endPos.get i ∧ 
                   0 ≤ start.get i ∧ start.get i ≤ (a.get i).length ∧
                   0 ≤ endPos.get i ∧ endPos.get i ≤ (a.get i).length ∧ 
                   sub.get i ≠ ""⌝⦄
    count a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Result is non-negative
      result.get i ≥ 0 ∧
      -- If substring is empty, count is 0 (handled by precondition)
      -- If substring is longer than search range, count is 0
      ((sub.get i).length > Int.natAbs (endPos.get i - start.get i) → result.get i = 0) ∧
      -- The count represents the maximum number of non-overlapping occurrences
      (∃ positions : List Nat,
        -- All positions are valid and within the specified range
        (∀ p ∈ positions, 
          Int.natAbs (start.get i) ≤ p ∧ 
          p + (sub.get i).length ≤ Int.natAbs (endPos.get i) ∧
          p + (sub.get i).length ≤ (a.get i).length ∧
          -- The substring matches at this position (simplified check)
          ((a.get i).drop p).take (sub.get i).length = sub.get i) ∧
        -- Positions are sorted and non-overlapping
        (positions.Pairwise (· ≤ ·)) ∧
        (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
          positions[j]! + (sub.get i).length ≤ positions[k]!) ∧
        -- The result equals the number of positions found
        result.get i = positions.length ∧
        -- This is the maximum possible count (optimality)
        (∀ other_positions : List Nat,
          (∀ p ∈ other_positions, 
            Int.natAbs (start.get i) ≤ p ∧ 
            p + (sub.get i).length ≤ Int.natAbs (endPos.get i) ∧
            p + (sub.get i).length ≤ (a.get i).length ∧
            ((a.get i).drop p).take (sub.get i).length = sub.get i) ∧
          (other_positions.Pairwise (· ≤ ·)) ∧
          (∀ j k : Nat, j < k → j < other_positions.length → k < other_positions.length →
            other_positions[j]! + (sub.get i).length ≤ other_positions[k]!) →
          other_positions.length ≤ positions.length))
    ⌝⦄ := by
  sorry
-- </vc-theorems>