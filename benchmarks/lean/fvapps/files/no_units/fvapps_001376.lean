-- <vc-preamble>
def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_puppy_path (N M : Nat) (coords : List (Nat × Nat)) (path : List Char) : List Int := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_length_matches_path_length {N M : Nat} {coords : List (Nat × Nat)} {path : List Char} :
  List.length (solve_puppy_path N M coords path) = List.length path := by
  sorry

theorem result_changes_bounded {N M : Nat} {coords : List (Nat × Nat)} {path : List Char} :
  ∀ i, i + 1 < List.length (solve_puppy_path N M coords path) → 
    let result := solve_puppy_path N M coords path;
    abs (result[i]! - result[i+1]!) ≤ 2 * N := by
  sorry

theorem empty_path {N M : Nat} :
  solve_puppy_path N M [(0,0)] [] = [] := by
  sorry
-- </vc-theorems>