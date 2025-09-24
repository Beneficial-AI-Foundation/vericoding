-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_jumps (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_jumps_nonnegative (s : String) :
  0 ≤ solve_jumps s :=
  sorry

theorem solve_jumps_bounded_by_gaps (s : String) :
  solve_jumps s ≤ (s.data.filter (· = '.') |>.length) :=
  sorry

theorem solve_jumps_trivial_cases1 :
  solve_jumps "####" = 0 :=
  sorry

theorem solve_jumps_trivial_cases2 :
  solve_jumps "#.#" = 1 :=
  sorry

theorem solve_jumps_single_gap (n : Nat) (h : n > 0) :
  let passage := "#" ++ String.mk (List.replicate n '.') ++ "#"
  solve_jumps passage = 1 :=
  sorry
-- </vc-theorems>