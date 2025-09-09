/-
You are given positive integers $L$ and $R$. You have to find the sum
S=∑i=LR(L∧(L+1)∧…∧i),S=∑i=LR(L∧(L+1)∧…∧i),S = \sum_{i=L}^R \left(L \wedge (L+1) \wedge \ldots \wedge i\right) \,,
where $\wedge$ denotes the bitwise AND operation. Since the sum could be large, compute it modulo $10^9+7$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $L$ and $R$.

-----Output-----
For each test case, print a single line containing one integer — the sum $S$ modulo $10^9+7$.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le L \le R \le 10^{18}$

-----Example Input-----
2
1 4
4 10

-----Example Output-----
1
16

-----Explanation-----
Example case 1: The sum is 1 + 1 AND 2 + 1 AND 2 AND 3 + 1 AND 2 AND 3 AND 4 = 1 + 0 + 0 + 0 = 1.
Example case 2: The sum is 4 + 4 AND 5 + 4 AND 5 AND 6 + 4 AND 5 AND 6 AND 7 + … + 4 AND 5 AND … AND 10 = 4 + 4 + … + 0 = 16.
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_sum (l r : Nat) : Nat :=
  sorry

theorem calculate_sum_range_bounds (l r : Nat)
  (h1 : 1 ≤ l) (h2 : l ≤ r) (h3 : r ≤ 1000) : 
  0 ≤ calculate_sum l r ∧ calculate_sum l r ≤ 1000000007 :=
  sorry

theorem calculate_sum_identity (n : Nat)
  (h : 1 ≤ n ∧ n ≤ 1000) :
  calculate_sum n n = n :=
  sorry 

theorem calculate_sum_commutative (l r : Nat)
  (h1 : 1 ≤ l) (h2 : l ≤ r) (h3 : r ≤ 1000) :
  calculate_sum l r = calculate_sum l r :=
  sorry

theorem calculate_sum_consecutive (n : Nat) 
  (h : 1 ≤ n ∧ n ≤ 100) :
  calculate_sum n (n + 1) = (n + (n &&& (n + 1))) % 1000000007 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_sum 1 4

/-
info: 16
-/
-- #guard_msgs in
-- #eval calculate_sum 4 10

/-
info: 4
-/
-- #guard_msgs in
-- #eval calculate_sum 2 5

-- Apps difficulty: interview
-- Assurance level: unguarded