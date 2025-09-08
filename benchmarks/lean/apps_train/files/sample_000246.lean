/-
There are N workers.  The i-th worker has a quality[i] and a minimum wage expectation wage[i].
Now we want to hire exactly K workers to form a paid group.  When hiring a group of K workers, we must pay them according to the following rules:

Every worker in the paid group should be paid in the ratio of their quality compared to other workers in the paid group.
Every worker in the paid group must be paid at least their minimum wage expectation.

Return the least amount of money needed to form a paid group satisfying the above conditions.

Example 1:
Input: quality = [10,20,5], wage = [70,50,30], K = 2
Output: 105.00000
Explanation: We pay 70 to 0-th worker and 35 to 2-th worker.

Example 2:
Input: quality = [3,1,10,10,1], wage = [4,8,2,2,7], K = 3
Output: 30.66667
Explanation: We pay 4 to 0-th worker, 13.33333 to 2-th and 3-th workers seperately. 

Note:

1 <= K <= N <= 10000, where N = quality.length = wage.length
1 <= quality[i] <= 10000
1 <= wage[i] <= 10000
Answers within 10^-5 of the correct answer will be considered correct.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_cost_to_hire_workers (quality wage : List Int) (k : Int) : Float :=
  sorry

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

-- Apps difficulty: interview
-- Assurance level: unguarded