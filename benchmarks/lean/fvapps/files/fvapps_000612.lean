-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveSparrowProblem (n k : Nat) (classes : List Nat) (links : List (Nat × Nat)) : Int := sorry

def isValidTree (n : Nat) (links : List (Nat × Nat)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_int (n k : Nat) (classes : List Nat) (links : List (Nat × Nat)) :
  let result := solveSparrowProblem n k classes links
  result ≥ -1 := sorry

theorem tree_validation (n k : Nat) (classes : List Nat) (links : List (Nat × Nat)) :
  isValidTree n links = true → 
  let result := solveSparrowProblem n k classes links
  result ≥ -1 := sorry

theorem minimal_cases_solvable : 
  (let n₁ := 1; let k₁ := 1; let classes₁ := [1]; let links₁ := [];
   solveSparrowProblem n₁ k₁ classes₁ links₁ ≥ 0) ∧
  (let n₂ := 2; let k₂ := 1; let classes₂ := [1,1]; let links₂ := [(1,2)];
   solveSparrowProblem n₂ k₂ classes₂ links₂ ≥ 0) ∧
  (let n₃ := 2; let k₃ := 2; let classes₃ := [1,2]; let links₃ := [(1,2)];
   solveSparrowProblem n₃ k₃ classes₃ links₃ ≥ 0) := sorry

theorem impossible_case :
  let n := 3; let k := 4; let classes := [1,2,3]; let links := [(1,2), (1,3)];
  solveSparrowProblem n k classes links = -1 := sorry

theorem linear_tree_bounds (n k : Nat) (classes : List Nat) (links : List (Nat × Nat)) :
  n = 4 →
  k = 2 →
  classes = [1,2,1,2] →
  links = [(1,2), (2,3), (3,4)] →
  let result := solveSparrowProblem n k classes links
  result ≥ 0 ∧ result ≤ n := sorry
-- </vc-theorems>