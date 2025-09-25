-- <vc-preamble>
def solve_tree_labeling (N : Nat) (edges : List (Nat × Nat)) (K : Nat) 
    (labels : List (Nat × Int)) : Option (List Int) :=
  sorry

def valid_solution (g : Graph) (labels : List (Nat × Int)) (result : List Int) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int :=
  if x < 0 then -x else x
-- </vc-definitions>

-- <vc-theorems>
theorem line_graph_solution_valid {N K : Nat} {base : Int}
    (h1 : K ≤ N) (h2 : 0 < N) : 
    let edges := List.range (N-1) |>.map (fun i => (i+1, i+2))
    let labels := List.range K |>.map (fun i => (i+1, base - ↑i))
    match solve_tree_labeling N edges K labels with
    | none => ∀ i j, i < K → j < K → 
        abs (↑(labels.get! i).1 - ↑(labels.get! j).1) = 1 → 
        abs ((labels.get! i).2 - (labels.get! j).2) ≠ 1
    | some result => valid_solution ⟨N, edges⟩ labels result = true
    := sorry

theorem star_graph_solution_exists {N : Nat} {center : Int}
    (h : 2 < N) :
    let edges := List.range (N-1) |>.map (fun i => (1, i+2))
    let labels := [(1, center)]
    (solve_tree_labeling N edges 1 labels).isSome ∧
    match solve_tree_labeling N edges 1 labels with
    | none => False  
    | some result => valid_solution ⟨N, edges⟩ labels result = true
    := sorry
-- </vc-theorems>