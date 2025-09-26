-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generate_pairs (n : Nat) : List (Nat × Nat) := sorry

theorem generate_pairs_valid_bounds {n : Nat} :
  ∀ p, p ∈ generate_pairs n → 
    (Prod.fst p ≤ Prod.snd p) ∧ (Prod.snd p ≤ n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem generate_pairs_unique {n : Nat} :
  ∀ p₁ p₂, p₁ ∈ generate_pairs n → p₂ ∈ generate_pairs n →
    p₁ = p₂ ∨ p₁ ≠ p₂ := sorry

theorem generate_pairs_length {n : Nat} :
  (generate_pairs n).length = (n + 1) * (n + 2) / 2 := sorry

theorem generate_pairs_ordered {n : Nat} :
  ∀ p₁ p₂, p₁ ∈ generate_pairs n → p₂ ∈ generate_pairs n →
    (generate_pairs n).indexOf p₁ < (generate_pairs n).indexOf p₂ →
    p₁.1 < p₂.1 ∨ (p₁.1 = p₂.1 ∧ p₁.2 ≤ p₂.2) := sorry

/-
info: [[0, 0], [0, 1], [0, 2], [1, 1], [1, 2], [2, 2]]
-/
-- #guard_msgs in
-- #eval generate_pairs 2

/-
info: [[0, 0]]
-/
-- #guard_msgs in
-- #eval generate_pairs 0

/-
info: [[0, 0], [0, 1], [1, 1]]
-/
-- #guard_msgs in
-- #eval generate_pairs 1
-- </vc-theorems>