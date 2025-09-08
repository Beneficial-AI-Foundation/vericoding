/-
The chef is trying to solve some series problems, Chef wants your help to code it. Chef has one number N. Help the chef to find N'th number in the series.
0, 1, 5, 14, 30, 55 …..

-----Input:-----
- First-line will contain $T$, the number of test cases. Then the test cases follow. 
- Each test case contains a single line of input, one integer $N$. 

-----Output:-----
For each test case, output as the pattern.

-----Constraints-----
- $1 \leq T \leq 10^4$
- $1 \leq N \leq 10^4$

-----Sample Input:-----
3
1
7
8

-----Sample Output:-----
0
91
140
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_series (n : Nat) : Nat :=
  sorry

theorem solve_series_output_type {n : Nat} (h : n ≥ 1) :
  solve_series n ≥ 0 :=
sorry

theorem solve_series_base_case :
  solve_series 1 = 0 :=
sorry

theorem solve_series_strictly_increasing {n : Nat} (h : n ≥ 2) :
  solve_series n < solve_series (n + 1) :=
sorry

theorem solve_series_formula {n : Nat} (h : n ≥ 2) :
  solve_series n = ((n - 2 + 1) * (2 * (n - 2) + 3) * (n - 2 + 2)) / 6 :=
sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_series 1

/-
info: 91
-/
-- #guard_msgs in
-- #eval solve_series 7

/-
info: 140
-/
-- #guard_msgs in
-- #eval solve_series 8

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible