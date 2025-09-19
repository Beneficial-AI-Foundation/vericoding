-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_to_hire_workers (quality wage : List Int) (k : Int) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_to_hire_workers_positive
  {n : Nat}
  {quality wage : List Int}
  {k : Int}
  (hq : quality.length = n)
  (hw : wage.length = n)
  (hk : 1 ≤ k ∧ k ≤ n)
  (hqpos : ∀ x ∈ quality, 1 ≤ x ∧ x ≤ 100)  
  (hwpos : ∀ x ∈ wage, 1 ≤ x ∧ x ≤ 1000) :
  min_cost_to_hire_workers quality wage k > 0 := sorry

theorem min_cost_to_hire_workers_finite
  {n : Nat} 
  {quality wage : List Int}
  {k : Int}
  (hq : quality.length = n)
  (hw : wage.length = n) 
  (hk : 1 ≤ k ∧ k ≤ n)
  (hqpos : ∀ x ∈ quality, 1 ≤ x ∧ x ≤ 100)
  (hwpos : ∀ x ∈ wage, 1 ≤ x ∧ x ≤ 1000) :
  Float.isFinite (min_cost_to_hire_workers quality wage k) := sorry

theorem min_cost_to_hire_workers_unit_cost
  (k : Int)
  (hk : k = 1 ∨ k = 2) :
  min_cost_to_hire_workers [1, 1] [1, 1] k = Float.ofInt k := sorry

theorem min_cost_to_hire_workers_equal_ratio :
  Float.abs (min_cost_to_hire_workers [1, 2, 3] [2, 4, 6] 2 - 6) < 1e-5 := sorry
-- </vc-theorems>