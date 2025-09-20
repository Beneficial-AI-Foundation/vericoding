-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_salmon_game (n k : Nat) : List (Nat × Nat) := sorry 

theorem valid_edge_range {n k : Nat} {edges : List (Nat × Nat)}
  (h1 : n ≥ 2) (h2 : k ≥ 3) (h3 : k ≤ 2^n)
  (h4 : edges = solve_salmon_game n k) :
  ∀ (e : Nat × Nat), e ∈ edges → 
    e.1 < 2^n ∧ e.2 < 2^n ∧ e.1 ≠ e.2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_edge_count {n k : Nat} {edges : List (Nat × Nat)} 
  (h1 : n ≥ 2) (h2 : k ≥ 3) (h3 : k ≤ 2^n)
  (h4 : edges = solve_salmon_game n k) :
  edges.length = k := sorry

theorem forms_cycle {n k : Nat} {edges : List (Nat × Nat)}
  (h1 : n ≥ 2) (h2 : k ≥ 3) (h3 : k ≤ 2^n) 
  (h4 : edges = solve_salmon_game n k) :
  ∃ (start : Nat), start ∈ (edges.map Prod.fst) ∧
  ∃ (vertices : List Nat), vertices.length = k ∧
    vertices.head? = some start ∧
    ∀ i, i < k - 1 → 
      ∃ v1 v2, (v1, v2) ∈ edges ∧ 
      vertices.get? i = some v1 ∧ 
      vertices.get? (i+1) = some v2 := sorry

theorem special_case_k3 {n : Nat} {edges : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : edges = solve_salmon_game n 3) :
  edges = [(0,1), (1,3), (3,0)] := sorry

theorem special_case_k4_cycle {n : Nat} {edges : List (Nat × Nat)}
  (h1 : n ≥ 2)
  (h2 : edges = solve_salmon_game n 4) :
  edges.length = 4 ∧
  ∃ (start : Nat), start ∈ (edges.map Prod.fst) ∧
  ∃ (vertices : List Nat), vertices.length = 4 ∧
    vertices.head? = some start ∧
    ∀ i, i < 3 → 
      ∃ v1 v2, (v1, v2) ∈ edges ∧ 
      vertices.get? i = some v1 ∧ 
      vertices.get? (i+1) = some v2 := sorry
-- </vc-theorems>