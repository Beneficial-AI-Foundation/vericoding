-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_chef_entries (a b : Nat) : Nat × Nat := sorry

theorem min_leq_max {a b : Nat} :
  let (min, max) := count_chef_entries a b
  min ≤ max := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_geq_max_input {a b : Nat} :
  let (min, max) := count_chef_entries a b 
  min ≥ (if a ≥ b then a else b) := sorry 

theorem max_leq_sum {a b : Nat} :
  let (min, max) := count_chef_entries a b
  max ≤ a + b := sorry

theorem min_eq_max_conditions {a b : Nat} :
  let (min, max) := count_chef_entries a b
  min = max → (a = 0 ∨ b = 0 ∨ a = b) := sorry

theorem zero_pair_equals_nonzero {x : Nat} :
  let (min1, max1) := count_chef_entries x 0
  let (min2, max2) := count_chef_entries 0 x
  (min1 = max1 ∧ min1 = x) ∧ (min2 = max2 ∧ min2 = x) := sorry
-- </vc-theorems>