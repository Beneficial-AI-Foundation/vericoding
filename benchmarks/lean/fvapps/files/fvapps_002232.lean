-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_beautiful_contest (n : Nat) (scores : List Nat) : Nat × Nat × Nat := sorry

theorem solve_beautiful_contest_identical_scores {n : Nat} {x : Nat}
  (h : x > 0) :
  solve_beautiful_contest n (List.replicate n x) = (0,0,0) := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>