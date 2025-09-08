/-
2021 was approaching and the world was about to end. So 2 gods Saurabhx and Saurabhy (from Celesta) created the Cyberverse. But this time disappointed with humans both the gods decided not to have humans in this world. So they created a world of cyborgs. A world without humans. Isn’t it interesting? So let us dive into the cyberverse and have a look at their problems.
There are $N$ kid cyborgs with Chief Cyborg '100gods' and he has $K$ weapons with him. He wants to distribute those $K$ weapons among $N$ kid cyborgs. Since all the kid cyborgs are very good friends, so they set a rule among themselves for taking those weapons. The rule states that the difference between kid cyborg having the maximum weapons and the kid cyborg having minimum weapons should be less than or equal to $1$.

Find the value of the minimum number of weapons a kid cyborg can have when all the $K$ weapons are distributed among them.

-----Input:-----
- The first line contains an integer $T$, denoting the number of test cases.
- Each of the next $T$ lines will contain two space-separated integers denoting $N$ and $K$ respectively.

-----Output:-----
- For each test case ,output a single line containing an integer $X$ denoting the minimum number of weapons a kid cyborg can have in that test case.  

-----Constraints:-----
- $1 \leq T \leq 10^5$
- $1 \leq N \leq 10^5$
- $1 \leq K \leq 10^9$

-----Sample Input:-----
1
5 8

-----Expected Output:-----
1

-----Explanation-----
- There are $5$ kids and $8$ weapons.  
- Hence we will distribute the weapons such that $3$ kids have $2$ weapons each and the remaining $2$ kids have $1$ weapon each.  
- Hence the minimum number of weapons a kid cyborg has is $1$. (  That is, $min(1,2)$ = $1$ )
-/

-- <vc-helpers>
-- </vc-helpers>

def calculate_min_weapons (n k : Nat) : Nat :=
sorry

theorem min_weapons_div (n k : Nat) (h : n > 0) :
  calculate_min_weapons n k = k / n :=
sorry

theorem min_weapons_nonneg (n k : Nat) (h : n > 0) :
  calculate_min_weapons n k ≥ 0 :=
sorry

theorem min_weapons_times_n_le (n k : Nat) (h : n > 0) :
  (calculate_min_weapons n k) * n ≤ k :=
sorry

theorem min_weapons_plus_one_gt (n k : Nat) (h : n > 0) (h2 : k % n ≠ 0) :
  (calculate_min_weapons n k + 1) * n > k :=
sorry

theorem min_weapons_zero (n : Nat) (h : n > 0) :
  calculate_min_weapons n 0 = 0 :=
sorry

theorem min_weapons_zero_n (k : Nat) :
  calculate_min_weapons 0 k = 0 ∨ calculate_min_weapons 0 k = undefined :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 5 8

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 3 7

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_min_weapons 10 25

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible