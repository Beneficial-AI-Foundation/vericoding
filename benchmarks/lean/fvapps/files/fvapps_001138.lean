-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def choose_team (n k : Nat) : Nat := sorry

theorem non_negative (n k : Nat) : 0 ≤ choose_team n k := by sorry
-- </vc-definitions>

-- <vc-theorems>
theorem k_greater_than_n (n k : Nat) : k > n → choose_team n k = 0 := by sorry

theorem k_equals_0_or_n (n k : Nat) : n > 0 ∧ (k = 0 ∨ k = n) → choose_team n k = 1 := by sorry

theorem symmetry (n k : Nat) : k ≤ n → choose_team n k = choose_team n (n-k) := by sorry

theorem pascal_triangle (n k : Nat) : 
  n > 0 ∧ k > 0 ∧ k < n → 
  choose_team n k = choose_team (n-1) (k-1) + choose_team (n-1) k := by sorry

theorem ones_property (n : Nat) : 
  n > 0 → choose_team n 0 = 1 ∧ choose_team n n = 1 := by sorry
-- </vc-theorems>