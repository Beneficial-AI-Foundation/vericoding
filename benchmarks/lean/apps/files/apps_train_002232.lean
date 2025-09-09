-- <vc-helpers>
-- </vc-helpers>

def solve_beautiful_contest (n : Nat) (scores : List Nat) : Nat × Nat × Nat := sorry

theorem solve_beautiful_contest_identical_scores {n : Nat} {x : Nat}
  (h : x > 0) :
  solve_beautiful_contest n (List.replicate n x) = (0,0,0) := sorry

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible