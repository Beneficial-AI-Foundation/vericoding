-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shuffleIt {α : Type} : List α → List (Nat × Nat) → List α
  | xs, swaps => sorry

def swapAt {α : Type} (xs : List α) (i j : Nat) (h₁ : i < xs.length) (h₂ : j < xs.length) : List α :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shuffleIt_preserves_length {α : Type} (xs : List α) (swaps : List (Nat × Nat))
  (h : ∀ p ∈ swaps, p.1 < xs.length ∧ p.2 < xs.length) :
  (shuffleIt xs swaps).length = xs.length :=
sorry

theorem shuffleIt_preserves_elements {α : Type} [BEq α] (xs : List α) (swaps : List (Nat × Nat))
  (h : ∀ p ∈ swaps, p.1 < xs.length ∧ p.2 < xs.length) :
  ∀ x, x ∈ xs ↔ x ∈ shuffleIt xs swaps :=
sorry

theorem shuffleIt_no_swaps {α : Type} (xs : List α) :
  shuffleIt xs [] = xs :=
sorry

theorem shuffleIt_single_swap {α : Type} (xs : List α) (i j : Nat)
  (h₁ : i < xs.length) (h₂ : j < xs.length) :
  shuffleIt xs [(i,j)] = swapAt xs i j h₁ h₂ :=
sorry
-- </vc-theorems>