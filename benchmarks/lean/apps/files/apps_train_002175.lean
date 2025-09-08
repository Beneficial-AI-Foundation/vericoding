/-
Johnny has just found the new, great tutorial: "How to become a grandmaster?". The tutorial tells many strange and unexpected for Johnny things, such as you have to be patient or that very important is solving many harder and harder problems. 

The boy has found an online judge with tasks divided by topics they cover. He has picked $p^{k_i}$ problems from $i$-th category ($p$ is his favorite number). He wants to solve them in two weeks (the patience condition is too hard for Johnny, so for simplicity, he looks only at easy tasks, which can be solved in such a period). Now our future grandmaster has to decide which topics to cover first and which the second week. Help him assign topics in such a way, that workload is balanced.

Formally, given $n$ numbers $p^{k_i}$, the boy wants to divide them into two disjoint sets, minimizing the absolute difference between sums of numbers in each set. Find the minimal absolute difference. Output the result modulo $10^{9}+7$.

-----Input-----

Input consists of multiple test cases. The first line contains one integer $t$ $(1 \leq t \leq 10^5)$ — the number of test cases. Each test case is described as follows:

The first line contains two integers $n$ and $p$ $(1 \leq n, p \leq 10^6)$. The second line contains $n$ integers $k_i$ $(0 \leq k_i \leq 10^6)$.

The sum of $n$ over all test cases doesn't exceed $10^6$.

-----Output-----

Output one integer — the reminder of division the answer by $1\,000\,000\,007$.

-----Example-----
Input
4
5 2
2 3 4 4 3
3 1
2 10 1000
4 5
0 1 1 100
1 8
89

Output
4
1
146981438
747093407

-----Note-----

You have to minimize the difference, not it's remainder. For example, if the minimum difference is equal to $2$, but there is also a distribution where the difference is $10^9 + 8$, then the answer is $2$, not $1$.

In the first test case of the example, there're the following numbers: $4$, $8$, $16$, $16$, and $8$. We can divide them into such two sets: ${4, 8, 16}$ and ${8, 16}$. Then the difference between the sums of numbers in sets would be $4$.
-/

def MOD := 1000000007

def List.sort (l: List Nat) : List Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def solve_minimized_workload (n: Nat) (p: Nat) (workloads: List Nat) : Nat :=
  sorry

theorem workload_result_bounds (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p > 0) (h4: p ≤ 10)
  (h5: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h6: workloads.length > 0) (h7: workloads.length ≤ 100) :
  let result := solve_minimized_workload n p workloads
  0 ≤ result ∧ result < MOD :=
sorry

theorem workload_p_one_special_case (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p = 1)
  (h4: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h5: workloads.length > 0) (h6: workloads.length ≤ 100) :
  let result := solve_minimized_workload n p workloads
  result = n % 2 ∧ (result = 0 ∨ result = 1) :=
sorry

theorem workload_sort_invariant (n p: Nat) (workloads: List Nat)
  (h1: n > 0) (h2: n ≤ 100) (h3: p > 0) (h4: p ≤ 10)
  (h5: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h6: workloads.length > 0) (h7: workloads.length ≤ 100) :
  solve_minimized_workload n p workloads = 
  solve_minimized_workload n p (List.sort workloads) :=
sorry

theorem workload_length_matches_n (p: Nat) (workloads: List Nat)
  (h1: p > 0) (h2: p ≤ 10)
  (h3: ∀ w ∈ workloads, w ≥ 0 ∧ w ≤ 1000)
  (h4: workloads.length > 0) (h5: workloads.length ≤ 100) :
  let n := workloads.length
  let result := solve_minimized_workload n p workloads
  0 ≤ result ∧ result < MOD :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_minimized_workload 5 2 [2, 3, 4, 4, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_minimized_workload 3 1 [2, 10, 1000]

/-
info: 146981438
-/
-- #guard_msgs in
-- #eval solve_minimized_workload 4 5 [0, 1, 1, 100]

-- Apps difficulty: competition
-- Assurance level: unguarded