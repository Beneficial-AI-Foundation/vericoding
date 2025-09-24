-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_shortest_path (n : Nat) (edges : List (Nat × Nat)) : Nat := sorry

theorem find_shortest_path_in_modulo_range (n : Nat) (edges : List (Nat × Nat))
  (hn : n ≥ 2) :
  0 ≤ find_shortest_path n edges ∧ find_shortest_path n edges < 998244353 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_shortest_path_cycle_bound (n : Nat) 
  (hn : n ≥ 2)
  (edges : List (Nat × Nat))
  (h_edges : edges = (List.range (n-1)).map (λ i => (i+1, i+2)) ++ [(n,1)]) :
  find_shortest_path n edges ≤ n := sorry

theorem find_shortest_path_basic_single_edge :
  find_shortest_path 2 [(2,1)] = 2 := sorry

theorem find_shortest_path_basic_disconnected :
  find_shortest_path 3 [(1,2)] = 536870912 := sorry
-- </vc-theorems>