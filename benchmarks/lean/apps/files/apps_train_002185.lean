-- <vc-helpers>
-- </vc-helpers>

def find_sequence (k n : Nat) : List Nat :=
  sorry

theorem sequence_values {k n : Nat} (h1 : k ≥ 1) (h2 : n ≥ 1) :
  let seq := find_sequence k n
  ∀ x ∈ seq, 0 < x ∧ x ≤ k :=
  sorry

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible