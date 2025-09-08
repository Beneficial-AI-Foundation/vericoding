/-
Tomya is a girl. She loves Chef Ciel very much.

Today, too, Tomya is going to Ciel's restaurant.
Of course, Tomya would like to go to Ciel's restaurant as soon as possible.
Therefore Tomya uses one of the shortest paths from Tomya's house to Ciel's restaurant.
On the other hand, Tomya is boring now to use the same path many times.
So Tomya wants to know the number of shortest paths from Tomya's house to Ciel's restaurant.
Your task is to calculate the number under the following assumptions.

This town has N intersections and M two way roads.
The i-th road connects from the Ai-th intersection to the Bi-th intersection, and its length is 

Ci.
Tomya's house is in the 1st intersection, and Ciel's restaurant is in the N-th intersection.

-----Input-----

The first line contains an integer T, the number of test cases.
Then T test cases follow.
The first line of each test case contains 2 integers N, M.
Then next M lines contains 3 integers denoting Ai, Bi and Ci.

-----Output-----

For each test case, print the number of shortest paths from Tomya's house to Ciel's restaurant.

-----Constraints-----

1 ≤ T ≤ 10

2 ≤ N ≤ 10

1 ≤ M ≤ N ∙ (N – 1) / 2

1 ≤ Ai, Bi ≤ N

1 ≤ Ci ≤ 10
Ai ≠ Bi

If i ≠ j and Ai = Aj, then Bi ≠ Bj

There is at least one path from Tomya's house to Ciel's restaurant.

-----Sample Input-----
2
3 3
1 2 3
2 3 6
1 3 7
3 3
1 2 3
2 3 6
1 3 9

-----Sample Output-----
1
2

-----Explanations-----

In the first sample, only one shortest path exists, which is 1-3.

In the second sample, both paths 1-2-3 and 1-3 are the shortest paths.
-/

def Edge := Nat × Nat × Nat
def Graph := List Edge

-- <vc-helpers>
-- </vc-helpers>

def count_shortest_paths (n : Nat) (edges : Graph) : Nat :=
  sorry

theorem count_paths_positive 
  (n : Nat) (edges : Graph) 
  (h1 : n ≥ 2)
  (h2 : edges.length > 0) :
  count_shortest_paths n edges > 0 := 
  sorry

theorem count_paths_permutation_invariant
  (n : Nat) (edges1 edges2 : Graph)
  (h : edges2 = edges1) :
  count_shortest_paths n edges1 = count_shortest_paths n edges2 :=
  sorry

theorem count_paths_weight_order_invariant
  (n : Nat) (edges edges_rev : Graph)
  (h : edges_rev = edges) :
  count_shortest_paths n edges = count_shortest_paths n edges_rev :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_shortest_paths 3 [(1, 2, 3), (2, 3, 6), (1, 3, 7)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_shortest_paths 3 [(1, 2, 3), (2, 3, 6), (1, 3, 9)]

-- Apps difficulty: interview
-- Assurance level: unguarded