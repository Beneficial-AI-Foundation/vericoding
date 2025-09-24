-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_quantifiers (n m : Nat) (edges : List (Nat × Nat)) : (Nat × String) ⊕ Unit := sorry

def has_cycle (n : Nat) (edges : List (Nat × Nat)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_quantifiers_output_format {n m : Nat} {edges : List (Nat × Nat)}
  (h_edges : ∀ (e : Nat × Nat), e ∈ edges → e.1 ≤ n ∧ e.2 ≤ n ∧ e.1 ≠ e.2) :
  match solve_quantifiers n m edges with
  | .inl (num_universal, quantifiers) =>
    quantifiers.length = n ∧ 
    (∀ c, c ∈ quantifiers.data → c = 'A' ∨ c = 'E') ∧
    num_universal = (quantifiers.data.filter (· = 'A')).length
  | .inr _ => True
  := sorry

theorem solve_quantifiers_cycles {n m : Nat} {edges : List (Nat × Nat)}
  (h_edges : ∀ (e : Nat × Nat), e ∈ edges → e.1 ≤ n ∧ e.2 ≤ n ∧ e.1 ≠ e.2) :
  has_cycle n edges = true → solve_quantifiers n m edges = .inr () := sorry

theorem solve_quantifiers_empty {n : Nat} :
  solve_quantifiers n 0 [] = .inl (n, String.mk (List.replicate n 'A')) := sorry

theorem solve_quantifiers_edge_cases_one :
  solve_quantifiers 1 0 [] = .inl (1, "A") := sorry

theorem solve_quantifiers_edge_cases_two :
  solve_quantifiers 2 0 [] = .inl (2, "AA") := sorry

theorem solve_quantifiers_edge_cases_three :
  solve_quantifiers 3 2 [(1,2), (2,3)] = .inl (3, "AAA") := sorry
-- </vc-theorems>