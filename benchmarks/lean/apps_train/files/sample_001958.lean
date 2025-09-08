/-
Arkady needs your help again! This time he decided to build his own high-speed Internet exchange point. It should consist of n nodes connected with minimum possible number of wires into one network (a wire directly connects two nodes). Exactly k of the nodes should be exit-nodes, that means that each of them should be connected to exactly one other node of the network, while all other nodes should be connected to at least two nodes in order to increase the system stability.

Arkady wants to make the system as fast as possible, so he wants to minimize the maximum distance between two exit-nodes. The distance between two nodes is the number of wires a package needs to go through between those two nodes.

Help Arkady to find such a way to build the network that the distance between the two most distant exit-nodes is as small as possible.

-----Input-----

The first line contains two integers n and k (3 ≤ n ≤ 2·10^5, 2 ≤ k ≤ n - 1) — the total number of nodes and the number of exit-nodes.

Note that it is always possible to build at least one network with n nodes and k exit-nodes within the given constraints.

-----Output-----

In the first line print the minimum possible distance between the two most distant exit-nodes. In each of the next n - 1 lines print two integers: the ids of the nodes connected by a wire. The description of each wire should be printed exactly once. You can print wires and wires' ends in arbitrary order. The nodes should be numbered from 1 to n. Exit-nodes can have any ids.

If there are multiple answers, print any of them.

-----Examples-----
Input
3 2

Output
2
1 2
2 3

Input
5 3

Output
3
1 2
2 3
3 4
3 5

-----Note-----

In the first example the only network is shown on the left picture.

In the second example one of optimal networks is shown on the right picture.

Exit-nodes are highlighted. [Image]
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_network (n k : Nat) : NetworkSolution :=
  sorry

theorem solve_network_valid (n k : Nat) (h1: n ≥ 2) (h2: k ≥ 1) (h3: k < n) :
  let sol := solve_network n k
  -- Network has valid size
  (sol.connections.length = n - 1) ∧  
  -- All nodes are in valid range
  (∀ (u v : Nat), (u, v) ∈ sol.connections → u ≤ n ∧ v ≤ n) ∧
  -- No duplicate connections
  (∀ (u v : Nat), (u, v) ∈ sol.connections → (v, u) ∉ sol.connections) ∧
  -- First node has k children
  (sol.connections.filter (fun (p : Nat × Nat) => p.1 = 1)).length = k ∧
  -- Other nodes have exactly one parent
  (∀ v : Nat, v ≠ 1 → v ≤ n → 
    (sol.connections.filter (fun p => p.2 = v)).length = 1) :=
  sorry

theorem solve_network_distance_positive (n k : Nat) (h1: n ≥ 2) (h2: k ≥ 1) (h3: k < n) :
  (solve_network n k).min_dist > 0 :=
  sorry

theorem solve_network_monotone_n (n k : Nat) (h1: n > k + 2) (h2: k ≥ 1) :
  (solve_network n k).min_dist ≥ (solve_network (n-1) k).min_dist :=
  sorry

theorem solve_network_monotone_k (n k : Nat) (h1: n ≥ 2) (h2: k > 1) (h3: k < n) :
  (solve_network n k).min_dist ≤ (solve_network n (k-1)).min_dist :=
  sorry

/-
info: n - 1
-/
-- #guard_msgs in
-- #eval len conns

/-
info: n - 1
-/
-- #guard_msgs in
-- #eval len conns

/-
info: n - 1
-/
-- #guard_msgs in
-- #eval len conns

-- Apps difficulty: competition
-- Assurance level: unguarded