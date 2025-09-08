/-
There are n engineers numbered from 1 to n and two arrays: speed and efficiency, where speed[i] and efficiency[i] represent the speed and efficiency for the i-th engineer respectively. Return the maximum performance of a team composed of at most k engineers, since the answer can be a huge number, return this modulo 10^9 + 7.
The performance of a team is the sum of their engineers' speeds multiplied by the minimum efficiency among their engineers. 

Example 1:
Input: n = 6, speed = [2,10,3,1,5,8], efficiency = [5,4,3,9,7,2], k = 2
Output: 60
Explanation: 
We have the maximum performance of the team by selecting engineer 2 (with speed=10 and efficiency=4) and engineer 5 (with speed=5 and efficiency=7). That is, performance = (10 + 5) * min(4, 7) = 60.

Example 2:
Input: n = 6, speed = [2,10,3,1,5,8], efficiency = [5,4,3,9,7,2], k = 3
Output: 68
Explanation:
This is the same example as the first but k = 3. We can select engineer 1, engineer 2 and engineer 5 to get the maximum performance of the team. That is, performance = (2 + 10 + 5) * min(5, 4, 7) = 68.

Example 3:
Input: n = 6, speed = [2,10,3,1,5,8], efficiency = [5,4,3,9,7,2], k = 4
Output: 72

Constraints:

1 <= n <= 10^5
speed.length == n
efficiency.length == n
1 <= speed[i] <= 10^5
1 <= efficiency[i] <= 10^8
1 <= k <= n
-/

-- <vc-helpers>
-- </vc-helpers>

def max_performance (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat) : Nat := sorry

def MOD := 1000000007

theorem max_performance_mod (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat) :
  0 ≤ max_performance n speeds efficiencies k ∧ 
  max_performance n speeds efficiencies k < MOD := sorry

theorem max_performance_geq_single_max (n : Nat) (speeds : List Nat) (efficiencies : List Nat) (k : Nat)
  (h1 : speeds.length = n) (h2 : efficiencies.length = n) (h3 : k ≤ n) :
  ∃ maxProd : Nat, 
    maxProd = List.foldr (fun i acc => max acc ((speeds.get! i) * (efficiencies.get! i))) 0 (List.range n) ∧
    max_performance n speeds efficiencies k ≥ maxProd := sorry

theorem max_performance_monotone (n : Nat) (speeds : List Nat) (efficiencies : List Nat) 
  (k : Nat) (h1 : k > 1) (h2 : k ≤ n) :
  max_performance n speeds efficiencies k ≥ 
  max_performance n speeds efficiencies (k-1) := sorry

theorem max_performance_min_case :
  max_performance 1 [1] [1] 1 = 1 := sorry

theorem max_performance_k_one (n : Nat) (speeds : List Nat) (efficiencies : List Nat)
  (h1 : speeds = [2,1,3]) (h2 : efficiencies = [3,2,1]) (h3 : n = 3) :
  max_performance n speeds efficiencies 1 = 6 := sorry

/-
info: 60
-/
-- #guard_msgs in
-- #eval max_performance 6 [2, 10, 3, 1, 5, 8] [5, 4, 3, 9, 7, 2] 2

/-
info: 68
-/
-- #guard_msgs in
-- #eval max_performance 6 [2, 10, 3, 1, 5, 8] [5, 4, 3, 9, 7, 2] 3

/-
info: 72
-/
-- #guard_msgs in
-- #eval max_performance 6 [2, 10, 3, 1, 5, 8] [5, 4, 3, 9, 7, 2] 4

-- Apps difficulty: interview
-- Assurance level: unguarded