def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n

-- <vc-helpers>
-- </vc-helpers>

def solve_puppy_path (N M : Nat) (coords : List (Nat × Nat)) (path : List Char) : List Int := 
  sorry

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

/-
info: [4, 6, 6]
-/
-- #guard_msgs in
-- #eval solve_puppy_path 2 3 [(1, 2), (0, 1)] "RDL"

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval solve_puppy_path 1 2 [(1, 1)] "RD"

-- Apps difficulty: interview
-- Assurance level: guarded