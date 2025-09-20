-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_unique_bst (n : Nat) : Nat := sorry

theorem num_unique_bst_base_cases : 
  num_unique_bst 0 = 1 ∧ 
  num_unique_bst 1 = 1 ∧ 
  num_unique_bst 2 = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem num_unique_bst_positive (n : Nat) : 
  num_unique_bst n > 0 := sorry

theorem num_unique_bst_increasing (n : Nat) :
  n ≥ 2 → num_unique_bst n > num_unique_bst (n-1) := sorry

theorem num_unique_bst_deterministic (n : Nat) :
  num_unique_bst n = num_unique_bst n := sorry

theorem num_unique_bst_known_values :
  num_unique_bst 0 = 1 ∧
  num_unique_bst 1 = 1 ∧
  num_unique_bst 2 = 2 ∧
  num_unique_bst 3 = 5 ∧
  num_unique_bst 4 = 14 ∧
  num_unique_bst 5 = 42 ∧
  num_unique_bst 6 = 132 ∧
  num_unique_bst 7 = 429 := sorry
-- </vc-theorems>