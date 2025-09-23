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
-- </vc-theorems>