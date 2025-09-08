/-
So the Chef has become health conscious and is now lifting weights at the gym. But its his first time so the trainer gives him a simple job to do. 

He has been given a weight lifting rod and N heavy weights, each weighing 20, 21, .... , 2n-1. He has to stick each of the "N" weights on the rod, one after another, in such a way that the right side is never heavier than the left side. At each step he chooses one of the weights that has not yet been fixed on the rod, and fix it on either the left side of the rod or the right, until all of the weights have been placed.

Now help the chef and find out, in how many ways the chef can accomplish this?

-----Input-----
First line of input contains an integer T, the number of test cases. Then T test cases follow. Each line of test case contains one integer, N denoting the number of weights

-----Output-----
The output contains T lines, each containing an integer denoting all possible combinations

-----Example-----
Input:
3
2
5
18

Output:
3
945
221643095476699771875
-/

-- <vc-helpers>
-- </vc-helpers>

def count_weight_arrangements (n : Int) : Int := sorry

theorem small_known_values :
  (count_weight_arrangements 1 = 1) ∧ 
  (count_weight_arrangements 2 = 3) ∧
  (count_weight_arrangements 3 = 15) := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 2

/-
info: 945
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 5

/-
info: 221643095476699771875
-/
-- #guard_msgs in
-- #eval count_weight_arrangements 18

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible