-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_shortest_path (n: Nat) (x y: Nat) (edges: List (Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem star_graph_shortest_path {n x y: Nat} {edges : List (Nat × Nat)}
  (h1: n ≥ 3)
  (h2: edges = List.map (fun i => (1, i)) (List.range (n-1) |>.map (·+2)))
  (h3: x > y)
  : find_shortest_path n x y edges = (n-2)*y + x := by
  sorry

theorem minimal_graph_shortest_path {x y: Nat} {edges: List (Nat × Nat)}
  (h1: edges = [(1,2)])
  : find_shortest_path 2 x y edges = x ∨ find_shortest_path 2 x y edges = y := by
  sorry
-- </vc-theorems>