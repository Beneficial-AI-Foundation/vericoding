/-
Chef has a garden with $N$ plants arranged in a line in decreasing order of height. Initially the height of the plants are $A_1, A_2, ..., A_N$.
The plants are growing, after each hour the height of the $i$-th plant increases by $i$ millimeters. Find the minimum number of integer hours that Chef must wait to have two plants of the same height.

-----Input:-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space separated integers $A_1,A_2,..A_N$. 

-----Output:-----
For each test case print a single line containing one integer, the minimum number of integer hours that Chef must wait to have two plants of the same height.

-----Constraints-----
- $1 \leq T \leq 1000$
- $2 \leq N \leq 10^5$
- $0\leq A_i \leq 10^{18}$
- $A_i >A_{i+1}$, for each valid $i$
- The Sum of $N$ over all test cases does not exceed $10^6$

-----Sample Input:-----
1
3
8 4 2

-----Sample Output:-----
2

-----EXPLANATION:-----
After $2$ hours there are two plants with the same height. 
$[8,4,2] \rightarrow [9,6,5] \rightarrow [10,8,8]$.
-/

-- <vc-helpers>
-- </vc-helpers>

def min_hours_equal_plants (n : Nat) (plants : List Nat) : Nat := sorry

def isDecreasing (l : List Nat) : Prop :=
  ∀ i, i + 1 < l.length → l[i]! > l[i+1]!

theorem min_gap_strictly_decreasing
  {n : Nat} {plants : List Nat}
  (h_sorted : isDecreasing plants)
  (h_len : plants.length = n)
  (h_size : n ≥ 2)
  (h_bounded : ∀ x ∈ plants, x ≥ 1 ∧ x ≤ 1000) :
  ∃ i, i + 1 < plants.length ∧ 
    min_hours_equal_plants n plants = plants[i]! - plants[i+1]! :=
sorry

theorem min_gap_constant
  {n : Nat} {gap : Nat}
  (h_n : n ≥ 2 ∧ n ≤ 10)
  (h_gap : gap ≥ 1 ∧ gap ≤ 100)
  (plants := List.range n |>.map (fun i => 100 - i * gap)) :
  min_hours_equal_plants n plants = gap :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_hours_equal_plants 3 [8, 4, 2]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_hours_equal_plants 4 [10, 7, 4, 1]

/-
info: 4
-/
-- #guard_msgs in
-- #eval min_hours_equal_plants 5 [20, 15, 10, 5, 1]

-- Apps difficulty: interview
-- Assurance level: guarded