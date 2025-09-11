-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nice_sequence_swaps (n : Nat) (sequence : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_nice_sequence_swaps_is_natural (n : Nat) (sequence : List Int) :
  ∃ (result : Nat), count_nice_sequence_swaps n sequence = result :=
  sorry

theorem count_nice_sequence_swaps_non_negative (n : Nat) (sequence : List Int) :
  count_nice_sequence_swaps n sequence ≥ 0 :=
  sorry

theorem count_nice_sequence_swaps_preserves_input (n : Nat) (sequence : List Int) :
  let original := sequence;
  count_nice_sequence_swaps n original = count_nice_sequence_swaps n sequence :=
  sorry

theorem count_nice_sequence_swaps_monotonic_input (n : Nat) (sequence : List Int) :
  ∃ (result_asc result_desc : Nat),
    count_nice_sequence_swaps n sequence = result_asc ∧
    count_nice_sequence_swaps n sequence = result_desc :=
  sorry

theorem count_nice_sequence_swaps_small_values 
  {n : Nat} {sequence : List Int}
  (h₁ : ∀ x ∈ sequence, 1 ≤ x ∧ x ≤ 10)
  (h₂ : 1 ≤ sequence.length ∧ sequence.length ≤ 10) :
  ∃ (result : Nat), count_nice_sequence_swaps n sequence = result ∧ result ≥ 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_nice_sequence_swaps 5 [2, 8, 4, 7, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_nice_sequence_swaps 4 [200, 150, 100, 50]

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_nice_sequence_swaps 10 [3, 2, 1, 4, 1, 4, 1, 4, 1, 4]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded