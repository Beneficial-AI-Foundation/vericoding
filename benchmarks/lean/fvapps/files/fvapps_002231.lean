-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_permutation (n : Nat) (perm : List Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_permutation (n : Nat) (h : n > 0):
  let perm := List.range n
  solve_permutation n perm = 
    if n % 2 = 0 then "Petr" else "Um_nik" := by
  sorry

theorem single_swap (n : Nat) (h : n > 1):
  let perm := List.range n
  let swapped_perm := sorry -- swap first two elements
  solve_permutation n swapped_perm = 
    if n % 2 = 0 then "Um_nik" else "Petr" := by
  sorry

theorem result_is_valid (n : Nat) (h : n > 0) (perm : List Nat):
  solve_permutation n perm = "Petr" ∨ 
  solve_permutation n perm = "Um_nik" := by
  sorry
-- </vc-theorems>