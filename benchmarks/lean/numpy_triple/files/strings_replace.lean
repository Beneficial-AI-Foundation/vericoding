-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def replace {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem replace_spec {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) :
    ⦃⌜∀ i : Fin n, count.get i = 0 ∨ old.get i ≠ ""⌝⦄
    replace a old new count
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Zero count behavior: if count is 0, no replacements occur
      (count.get i = 0 → result.get i = a.get i) ∧
      -- Identity property: if old doesn't occur, result equals original
      ((∀ pos : Nat, pos + (old.get i).length ≤ (a.get i).length → 
        ¬(((a.get i).drop pos).take (old.get i).length = old.get i)) → 
        result.get i = a.get i) ∧
      -- Basic replacement property: result contains the transformed string
      (∃ (num_replacements : Nat),
        -- Number of replacements is bounded by count (if non-negative)
        (count.get i ≥ 0 → num_replacements ≤ Int.natAbs (count.get i)) ∧
        -- If count is negative, all possible non-overlapping occurrences are replaced
        (count.get i < 0 → 
          ∃ positions : List Nat,
            positions.length = num_replacements ∧
            (∀ p ∈ positions, 
              p + (old.get i).length ≤ (a.get i).length ∧
              ((a.get i).drop p).take (old.get i).length = old.get i) ∧
            -- Positions are sorted and non-overlapping
            (positions.Pairwise (· ≤ ·)) ∧
            (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
              positions[j]! + (old.get i).length ≤ positions[k]!)) ∧
        -- If count is non-negative, we replace min(count, total_occurrences)
        (count.get i ≥ 0 → 
          ∃ total_occurrences : Nat,
            num_replacements = min (Int.natAbs (count.get i)) total_occurrences ∧
            (∃ positions : List Nat,
              positions.length = total_occurrences ∧
              (∀ p ∈ positions, 
                p + (old.get i).length ≤ (a.get i).length ∧
                ((a.get i).drop p).take (old.get i).length = old.get i) ∧
              -- Positions are sorted and non-overlapping
              (positions.Pairwise (· ≤ ·)) ∧
              (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
                positions[j]! + (old.get i).length ≤ positions[k]!))))
    ⌝⦄ := by
  sorry
-- </vc-theorems>