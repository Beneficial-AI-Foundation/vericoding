/-
Nadaca is a country with N$N$ cities. These cities are numbered 1$1$ through N$N$ and connected by M$M$ bidirectional roads. Each city can be reached from every other city using these roads.
Initially, Ryan is in city 1$1$. At each of the following K$K$ seconds, he may move from his current city to an adjacent city (a city connected by a road to his current city) or stay at his current city. Ryan also has Q$Q$ conditions (a1,b1),(a2,b2),…,(aQ,bQ)$(a_1, b_1), (a_2, b_2), \ldots, (a_Q, b_Q)$ meaning that during this K$K$-second trip, for each valid i$i$, he wants to be in city ai$a_i$ after exactly bi$b_i$ seconds.
Since you are very good with directions, Ryan asked you to tell him how many different trips he could make while satisfying all conditions. Compute this number modulo 109+7$10^9 + 7$. A trip is a sequence of Ryan's current cities after 1,2,…,K$1, 2, \ldots, K$ seconds.

-----Input-----
- The first line of the input contains a single integer T$T$ denoting the number of test cases. The description of T$T$ test cases follows.
- The first line of each test case contains three space-separated integers N$N$, M$M$ and K$K$.
- Each of the next M$M$ lines contains two space-separated integers u$u$ and v$v$ denoting a road between cities u$u$ and v$v$.
- The next line contains a single integer Q$Q$.
- Q$Q$ lines follow. For each i$i$ (1≤i≤Q$1 \le i \le Q$), the i$i$-th of these lines contains two space-separated integers ai$a_i$ and bi$b_i$.

-----Output-----
For each test case, print a single line containing one integer — the number of trips Ryan can make, modulo 109+7$10^9+7$.

-----Constraints-----
- 1≤T≤50$1 \le T \le 50$
- 1≤N,M,K,Q≤9,000$1 \le N, M, K, Q \le 9,000$
- 1≤ui,vi≤N$1 \le u_i, v_i \le N$ for each valid i$i$
- ui≠vi$u_i \neq v_i$ for each valid i$i$
- there is at most one road between each pair of cities
- each city is reachable from every other city
- 1≤ai≤N$1 \le a_i \le N$ for each valid i$i$
- 0≤bi≤K$0 \le b_i \le K$ for each valid i$i$
- the sum of N$N$ over all test cases does not exceed 9,000$9,000$
- the sum of K$K$ over all test cases does not exceed 9,000$9,000$
- the sum of M$M$ over all test cases does not exceed 9,000$9,000$
- the sum of Q$Q$ over all test cases does not exceed 9,000$9,000$

-----Subtasks-----
Subtask #1 (20 points):
- the sum of N$N$ over all test cases does not exceed 400$400$
- the sum of K$K$ over all test cases does not exceed 400$400$
- the sum of M$M$ over all test cases does not exceed 400$400$
- the sum of Q$Q$ over all test cases does not exceed 400$400$
Subtask #2 (80 points): original constraints

-----Example Input-----
3
4 3 3
1 2
1 3
1 4
0
4 3 3
1 2
1 3
1 4
1
2 2
4 3 3
1 2
1 3
1 4
1
2 1

-----Example Output-----
28
4
6
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_path_conditions (N M K : Nat) (roads : List (Nat × Nat)) (Q : Nat) 
  (conditions : List (Nat × Nat)) : Nat :=
sorry

theorem solve_path_conditions_result_nonnegative (N M K : Nat) 
  (roads : List (Nat × Nat)) (Q : Nat) (conditions : List (Nat × Nat)) :
  solve_path_conditions N M K roads Q conditions ≥ 0 := sorry

theorem solve_path_conditions_result_bounded (N M K : Nat)
  (roads : List (Nat × Nat)) (Q : Nat) (conditions : List (Nat × Nat)) :
  solve_path_conditions N M K roads Q conditions < 10^9 + 7 := sorry 

theorem single_node_no_conditions (K : Nat) :
  solve_path_conditions 1 0 K [] 0 [] = 1 := sorry

-- Captures test_empty_graph

theorem empty_graph :
  solve_path_conditions 1 0 1 [] 0 [] = 1 := sorry

-- Apps difficulty: interview
-- Assurance level: unguarded