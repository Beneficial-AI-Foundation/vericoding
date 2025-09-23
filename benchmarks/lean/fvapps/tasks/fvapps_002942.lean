-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def josephus (xs : List α) (k : Nat) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem josephus_contains_all_elements {α} (xs : List α) (k : Nat) (h : xs ≠ []) :
  List.length (josephus xs k) = List.length xs ∧ 
  ∀ x, x ∈ xs ↔ x ∈ josephus xs k :=
  sorry

theorem josephus_preserves_input {α} (xs : List α) (k : Nat) (h : 0 < k) :
  josephus xs k = josephus xs k :=
  sorry

theorem josephus_deterministic {α} (xs : List α) (k : Nat) (h : 0 < k) :
  josephus xs k = josephus xs k :=
  sorry

theorem josephus_k_one {α} (xs : List α) (h : xs ≠ []) :
  josephus xs 1 = xs :=
  sorry
-- </vc-theorems>