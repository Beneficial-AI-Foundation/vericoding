-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_components (n: Nat) (edges: List (Nat × Nat)) : Nat :=
  sorry

def is_tree (n: Nat) (edges: List (Nat × Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem line_graph_components {n: Nat} (h: n ≥ 2) :
  let edges := List.range (n-1) |>.map (λi => (i+1, i+2))
  find_max_components n edges = 1 :=
sorry
-- </vc-theorems>