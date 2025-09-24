-- <vc-preamble>
def find_max_route_cost (n : Nat) (edges : List Edge) : Nat := sorry

def exists_path (edges : List Edge) (u v : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_path_cost (edges : List Edge) (u v : Nat) : Nat := sorry

theorem small_graph_path_costs {n : Nat} {edges : List Edge} 
  (h1 : n = 3)
  (h2 : ∀ e ∈ edges, e.src ≤ 3 ∧ e.dst ≤ 3)
  (h3 : ∀ e ∈ edges, e.cost ≤ 100)
  (h4 : edges.length ≤ 3)
  (h5 : edges.length ≥ 2)
  (h6 : ∀ e ∈ edges, e.src ≠ e.dst) :
  ∀ u v : Nat, u < n → v < n → u ≠ v →
    if exists_path edges u v then
      shortest_path_cost edges u v ≤ find_max_route_cost n edges
    else True := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetry_property {n : Nat} {edges : List Edge}
  (h1 : n = 3)
  (h2 : ∀ e ∈ edges, e.src ≤ 3 ∧ e.dst ≤ 3)
  (h3 : ∀ e ∈ edges, e.cost ≤ 100)
  (h4 : edges.length ≤ 3)
  (h5 : edges.length ≥ 2)
  (h6 : ∀ e ∈ edges, e.src ≠ e.dst) :
  find_max_route_cost n edges = 
  find_max_route_cost n (edges.map (λ e => ⟨e.dst, e.src, e.cost⟩)) := sorry

/-
info: 19
-/
-- #guard_msgs in
-- #eval find_max_route_cost 4 [(1, 2, 10), (1, 3, 24), (2, 3, 2), (2, 4, 15), (3, 4, 7)]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_max_route_cost 4 [(1, 2, 1), (2, 3, 1), (3, 4, 1)]

/-
info: 15
-/
-- #guard_msgs in
-- #eval find_max_route_cost 3 [(1, 2, 5), (2, 3, 10), (3, 1, 20)]
-- </vc-theorems>