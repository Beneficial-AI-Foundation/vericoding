-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_tree (n : Nat) (edges : List (Nat × Nat)) : String := sorry

def is_valid_tree_properties (n : Nat) (edges : List (Nat × Nat)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_valid (n : Nat) (h : n = 1) :
  is_tree n [] = "YES" := sorry 

theorem tree_properties (n : Nat) (edges : List (Nat × Nat)) :
  is_tree n edges = "YES" → is_valid_tree_properties n edges = true := sorry

theorem line_graph_valid (n : Nat) (h : n ≥ 2) :
  let edges := List.range (n-1) |>.map (fun i => (i+1, i+2))
  is_tree n edges = "YES" := sorry

theorem cycle_invalid (n : Nat) (h : n ≥ 3) :
  let edges := (List.range (n-1) |>.map (fun i => (i+1, i+2))) ++ [(n, 1)]
  is_tree n edges = "NO" := sorry

theorem disconnected_invalid (n : Nat) (h : n ≥ 3) :
  let edges := [(1,2)] ++ 
    (if n > 3 then 
      List.range (n-3) |>.map (fun i => (i+3, i+4))
    else [])
  is_tree n edges = "NO" := sorry
-- </vc-theorems>