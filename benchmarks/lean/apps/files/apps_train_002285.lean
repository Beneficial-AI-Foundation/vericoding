-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (s : String) (c : Char := 'a') : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_single_char (s : String) :
  String.length s = 1 →
  solve s = (if s = "a" then 0 else 1)
  := sorry

theorem solve_edge_cases :
  solve "z" = 1 ∧
  solve "a" = 0
  := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve "bbdcaaaa"

/-
info: 7
-/
-- #guard_msgs in
-- #eval solve "asdfghjk"

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve "ceaaaabb"

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve "bbaaddcc"

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve "z"

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve "ac"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible