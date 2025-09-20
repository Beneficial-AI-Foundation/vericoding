-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def squareUp (n: Nat) : List Nat := sorry

theorem square_up_length (n: Nat) (h: n > 0) :
  (squareUp n).length = n * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_up_range (n: Nat) (h: n > 0) :
  ∀ x ∈ squareUp n, x ≥ 0 ∧ x ≤ n := sorry

theorem square_up_pattern (n: Nat) (h: n > 0) :
  ∀ i < n,
    let row := List.take ((i+1)*n) (List.drop (i*n) (squareUp n))
    ∀ j < n, 
      (j < (n-(i+1)) → List.get! row j = 0) ∧ 
      (j ≥ (n-(i+1)) → List.get! row j = i+1-(j-(n-(i+1)))) := sorry
-- </vc-theorems>