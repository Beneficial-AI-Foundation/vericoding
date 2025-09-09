-- <vc-helpers>
-- </vc-helpers>

def solve_jumps (s : String) : Nat :=
  sorry

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

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_jumps "####"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_jumps "##.#..#"

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_jumps "##..#.#"

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_jumps "##.#....#"

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible