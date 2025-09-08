/-
Chef is now a corporate person. He has to attend office regularly. But chef does not want to go to office, rather he wants to stay home and discover different recipes and cook them. 
In the office where chef works, has two guards who count how many times a person enters into the office building. Though the duty of a guard is 24 hour in a day, but sometimes they fall asleep during their duty and could not track the entry of a person in the office building. But one better thing is that they never fall asleep at the same time. At least one of them remains awake and counts who enters into the office.
Now boss of Chef wants to calculate how many times Chef has entered into the building. He asked to the guard and they give him two integers A and B, count of first guard and second guard respectively.
Help the boss to count the minimum and maximum number of times Chef could have entered into the office building.

-----Input-----
The first line of the input contains an integer T denoting the number of test cases. The description of the T test cases follows. 
Each test case consists of a line containing two space separated integers A and B.

-----Output-----
For each test case, output a single line containing two space separated integers, the minimum and maximum number of times Chef could have entered into the office building.

-----Constraints-----
- 1 ≤ T ≤ 100
- 0 ≤ A, B ≤ 1000000

-----Example-----
Input:
1
19 17

Output:
19 36
-/

-- <vc-helpers>
-- </vc-helpers>

def count_chef_entries (a b : Nat) : Nat × Nat := sorry

theorem min_leq_max {a b : Nat} :
  let (min, max) := count_chef_entries a b
  min ≤ max := sorry

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

/-
info: (19, 36)
-/
-- #guard_msgs in
-- #eval count_chef_entries 19 17

/-
info: (5, 7)
-/
-- #guard_msgs in
-- #eval count_chef_entries 5 2

/-
info: (10, 10)
-/
-- #guard_msgs in
-- #eval count_chef_entries 0 10

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible