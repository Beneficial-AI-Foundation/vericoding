-- <vc-preamble>
def solve_tree_queries (n : Nat) (sweetness : List Int) (edges : List (Nat × Nat))
  (queries : List QueryType) : List Int :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_tree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_tree_queries_outputs_len {n : Nat} {sweetness : List Int} 
  {edges : List (Nat × Nat)} {queries : List QueryType}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true) :
  (solve_tree_queries n sweetness edges queries).length = 
  (queries.filter (fun q => match q with 
                           | QueryType.get _ => true
                           | _ => false)).length :=
sorry 

theorem solve_tree_queries_outputs_integers {n : Nat} {sweetness : List Int}
  {edges : List (Nat × Nat)} {queries : List QueryType} 
  {result : List Int}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true)
  (h3 : result = solve_tree_queries n sweetness edges queries) :
  ∀ x, x ∈ result → x ∈ sweetness ∨ ∃ q, q ∈ queries ∧ (
    match q with
    | QueryType.update _ v => v = x
    | _ => False
  ) :=
sorry

theorem solve_tree_queries_idempotent {n : Nat} {sweetness : List Int}
  {edges : List (Nat × Nat)} {val : Int} {node : Nat}
  (h1 : sweetness.length = n)
  (h2 : is_tree n edges = true)
  (h3 : node ≤ n) :
  (solve_tree_queries n sweetness edges 
    [QueryType.update node val, QueryType.get node]).length = 1 :=
sorry
-- </vc-theorems>