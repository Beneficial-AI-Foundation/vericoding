-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def build_sequence (stages : List (List Nat)) (indices : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem append_only_sequence_length 
  (stages : List (List Nat)) (indices : List Nat)
  (h1 : ∀ s ∈ stages, s.length = 2 ∧ s[0]! = 1) :
  (build_sequence stages indices).length ≤ indices.length := by
  sorry

theorem append_only_sequence_elements
  (stages : List (List Nat)) (indices : List Nat)
  (h1 : ∀ s ∈ stages, s.length = 2 ∧ s[0]! = 1)
  (result := build_sequence stages indices)
  (stage_vals := stages.map (λ s => s[1]!)) :
  ∀ i < result.length,
    ∃ j, j ≤ indices[i]! ∧
    result[i]! ∈ stage_vals.take (j + 1) := by
  sorry
-- </vc-theorems>