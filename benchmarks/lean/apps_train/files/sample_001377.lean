/-
Pied Piper is a startup company trying to build a new Internet called Pipernet. Currently, they have $A$ users and they gain $X$ users everyday. There is also another company called Hooli, which has currently $B$ users and gains $Y$ users everyday.
Whichever company reaches $Z$ users first takes over Pipernet. In case both companies reach $Z$ users on the same day, Hooli takes over.
Hooli is a very evil company (like E-Corp in Mr. Robot or Innovative Online Industries in Ready Player One). Therefore, many people are trying to help Pied Piper gain some users.
Pied Piper has $N$ supporters with contribution values $C_1, C_2, \ldots, C_N$. For each valid $i$, when the $i$-th supporter contributes, Pied Piper gains $C_i$ users instantly. After contributing, the contribution value of the supporter is halved, i.e. $C_i$ changes to $\left\lfloor C_i / 2 \right\rfloor$. Each supporter may contribute any number of times, including zero. Supporters may contribute at any time until one of the companies takes over Pipernet, even during the current day.
Find the minimum number of times supporters must contribute (the minimum total number of contributions) so that Pied Piper gains control of Pipernet.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains six space-separated integers $N$, $A$, $B$, $X$, $Y$ and $Z$.
- The second line contains $N$ space-separated integers $C_1, C_2, \ldots, C_N$ — the initial contribution values.

-----Output-----
For each test case, if Hooli will always gain control of Pipernet, print a single line containing the string "RIP" (without quotes). Otherwise, print a single line containing one integer — the minimum number of times supporters must contribute.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 10^5$
- $1 \le A, B, X, Y, Z \le 10^9$
- $A, B < Z$
- $0 \le C_i \le 10^9$ for each valid $i$

-----Example Input-----
3
3 10 15 5 10 100
12 15 18
3 10 15 5 10 100
5 5 10
4 40 80 30 30 100
100 100 100 100

-----Example Output-----
4
RIP
1

-----Explanation-----
Example case 1: After $8$ days, Pied Piper will have $50$ users and Hooli will have $95$ users. Then, if each supporter contributes once, Pied Piper will also have $95$ users. After that, they still need $5$ more users, so supporter $3$ can contribute again, with $18/2 = 9$ more users. So the answer will be $4$.
Example case 2: There is no way to beat Hooli.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_pipernet (n a b x y z : Nat) (contributions : List Nat) : Nat ⊕ String := sorry 

theorem solve_pipernet_valid_output
  (n a b x y z : Nat) (contributions : List Nat) 
  (h1 : 0 < n ∧ n ≤ 100)
  (h2 : a ≤ 1000000)
  (h3 : b ≤ 1000000) 
  (h4 : x ≤ 1000)
  (h5 : 0 < y ∧ y ≤ 1000)
  (h6 : 0 < z ∧ z ≤ 1000000)
  (h7 : z > b)
  (h8 : ∀ c ∈ contributions, c ≤ 1000000)
  (h9 : contributions.length ≤ n) :
  match solve_pipernet n a b x y z contributions with
  | Sum.inr "RIP" => 
    let max_contrib := contributions.foldr (· + ·) 0
    let max_users := a + ((z - b - 1) / y) * x + max_contrib
    max_users < z
  | Sum.inl val => 0 ≤ val
  | _ => False
  := sorry

theorem solve_pipernet_zero_contributions
  (n : Nat)
  (h1 : 0 < n ∧ n ≤ 100) :
  solve_pipernet n 10 15 5 10 100 (List.replicate n 0) = Sum.inr "RIP" := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_pipernet 3 10 15 5 10 100 [12, 15, 18]

/-
info: 'RIP'
-/
-- #guard_msgs in
-- #eval solve_pipernet 3 10 15 5 10 100 [5, 5, 10]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_pipernet 4 40 80 30 30 100 [100, 100, 100, 100]

-- Apps difficulty: interview
-- Assurance level: unguarded