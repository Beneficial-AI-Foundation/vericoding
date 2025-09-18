-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def cooking_challenge (n m q : Nat) (challenges : List (Nat × Nat × Int)) (combos : List (Nat × Nat)) : List Nat := sorry

theorem cooking_challenge_output_length
  (n m q : Nat)
  (challenges : List (Nat × Nat × Int))
  (combos : List (Nat × Nat))
  : List.length (cooking_challenge n m q challenges combos) = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cooking_challenge_output_nonnegative 
  (n m q : Nat)
  (challenges : List (Nat × Nat × Int)) 
  (combos : List (Nat × Nat))
  : ∀ x ∈ cooking_challenge n m q challenges combos, x ≥ 0 := sorry

theorem cooking_challenge_output_natural
  (n m q : Nat)
  (challenges : List (Nat × Nat × Int))
  (combos : List (Nat × Nat))
  : ∀ x ∈ cooking_challenge n m q challenges combos, ∃ k : Nat, x = k := sorry
-- </vc-theorems>