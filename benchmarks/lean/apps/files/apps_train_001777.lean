-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def findCityWithSmallestReachable (n : Nat) (edges : List (Nat × Nat × Nat)) (threshold : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_index_result (n : Nat) (edges : List (Nat × Nat × Nat)) (threshold : Nat)
  (h1 : n > 0)
  (h2 : ∀ e ∈ edges, e.1 < n ∧ e.2.1 < n)
  (h3 : ∀ e ∈ edges, e.2.2 > 0)
  (h4 : ∀ e ∈ edges, e.1 ≠ e.2.1) : 
  let result := findCityWithSmallestReachable n edges threshold
  result < n :=
  sorry

theorem symmetric_result (n : Nat) (edges : List (Nat × Nat × Nat)) (threshold : Nat)
  (h1 : n > 0)
  (h2 : ∀ e ∈ edges, e.1 < n ∧ e.2.1 < n)
  (h3 : ∀ e ∈ edges, e.2.2 > 0)
  (h4 : ∀ e ∈ edges, e.1 ≠ e.2.1) :
  let swappedEdges := edges.map (fun e => (e.2.1, e.1, e.2.2))
  findCityWithSmallestReachable n edges threshold = 
  findCityWithSmallestReachable n swappedEdges threshold :=
  sorry

theorem single_vertex_empty_graph :
  findCityWithSmallestReachable 1 [] 1 = 0 :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_city_with_smallest_reachable 4 [[0, 1, 3], [1, 2, 1], [1, 3, 4], [2, 3, 1]] 4

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_city_with_smallest_reachable 5 [[0, 1, 2], [0, 4, 8], [1, 2, 3], [1, 4, 2], [2, 3, 1], [3, 4, 1]] 2
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded