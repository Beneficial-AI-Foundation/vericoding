/-
Codefortia is a small island country located somewhere in the West Pacific. It consists of $n$ settlements connected by $m$ bidirectional gravel roads. Curiously enough, the beliefs of the inhabitants require the time needed to pass each road to be equal either to $a$ or $b$ seconds. It's guaranteed that one can go between any pair of settlements by following a sequence of roads.

Codefortia was recently struck by the financial crisis. Therefore, the king decided to abandon some of the roads so that:

  it will be possible to travel between each pair of cities using the remaining roads only,  the sum of times required to pass each remaining road will be minimum possible (in other words, remaining roads must form minimum spanning tree, using the time to pass the road as its weight),  among all the plans minimizing the sum of times above, the time required to travel between the king's residence (in settlement $1$) and the parliament house (in settlement $p$) using the remaining roads only will be minimum possible. 

The king, however, forgot where the parliament house was. For each settlement $p = 1, 2, \dots, n$, can you tell what is the minimum time required to travel between the king's residence and the parliament house (located in settlement $p$) after some roads are abandoned?

-----Input-----

The first line of the input contains four integers $n$, $m$, $a$ and $b$ ($2 \leq n \leq 70$, $n - 1 \leq m \leq 200$, $1 \leq a < b \leq 10^7$) — the number of settlements and gravel roads in Codefortia, and two possible travel times. Each of the following lines contains three integers $u, v, c$ ($1 \leq u, v \leq n$, $u \neq v$, $c \in \{a, b\}$) denoting a single gravel road between the settlements $u$ and $v$, which requires $c$ minutes to travel.

You can assume that the road network is connected and has no loops or multiedges.

-----Output-----

Output a single line containing $n$ integers. The $p$-th of them should denote the minimum possible time required to travel from $1$ to $p$ after the selected roads are abandoned. Note that for each $p$ you can abandon a different set of roads.

-----Examples-----
Input
5 5 20 25
1 2 25
2 3 25
3 4 20
4 5 20
5 1 20

Output
0 25 60 40 20

Input
6 7 13 22
1 2 13
2 3 13
1 4 22
3 4 13
4 5 13
5 6 13
6 1 13

Output
0 13 26 39 26 13

-----Note-----

The minimum possible sum of times required to pass each road in the first example is $85$ — exactly one of the roads with passing time $25$ must be abandoned. Note that after one of these roads is abandoned, it's now impossible to travel between settlements $1$ and $3$ in time $50$.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_codefortia (n m a b : Nat) (edges : List (Nat × Nat × Nat)) : List Nat := sorry

theorem solve_codefortia_result_length {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  (solve_codefortia n m a b edges).length = n :=
sorry

theorem solve_codefortia_start_vertex {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  n ≥ 1 → List.get! (solve_codefortia n m a b edges) 0 = 0 :=
sorry 

theorem solve_codefortia_distances_nonneg {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  ∀ x ∈ solve_codefortia n m a b edges, x ≥ 0 :=
sorry

theorem solve_codefortia_min_graph_props {edges : List (Nat × Nat × Nat)} :
  edges.length = 1 →
  (∀ (u v w : Nat), (u,v,w) ∈ edges → u ≤ 2 ∧ v ≤ 2 ∧ w ≤ 2) →
  let result := solve_codefortia 2 1 1 2 edges
  result.length = 2 ∧ 
  List.get! result 0 = 0 ∧
  ∀ x ∈ result, x ≥ 0 :=
sorry

/-
info: [0, 25, 60, 40, 20]
-/
-- #guard_msgs in
-- #eval solve_codefortia 5 5 20 25 [(1, 2, 25), (2, 3, 25), (3, 4, 20), (4, 5, 20), (5, 1, 20)]

/-
info: [0, 13, 26, 39, 26, 13]
-/
-- #guard_msgs in
-- #eval solve_codefortia 6 7 13 22 [(1, 2, 13), (2, 3, 13), (1, 4, 22), (3, 4, 13), (4, 5, 13), (5, 6, 13), (6, 1, 13)]

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval solve_codefortia 2 1 1 2 [(2, 1, 1)]

-- Apps difficulty: competition
-- Assurance level: unguarded