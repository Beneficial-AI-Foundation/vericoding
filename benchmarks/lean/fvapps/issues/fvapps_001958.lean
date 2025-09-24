-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_network (n k : Nat) : NetworkSolution :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>