-- <vc-preamble>
def solve (s : String) : Int :=
  sorry

def isBalanced (s : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def repeated_parens (n : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_odd_length_returns_minus_one {s : String} :
  (s.length % 2 = 1) → solve s = -1 :=
  sorry

theorem solve_valid_solution_bound {s : String} :
  solve s ≥ 0 → solve s ≤ s.length :=
  sorry

theorem solve_empty_string :
  solve "" = 0 :=
  sorry

theorem solve_single_paren_left :
  solve "(" = -1 :=
  sorry

theorem solve_single_paren_right :
  solve ")" = -1 :=
  sorry

theorem solve_reversed_pair :
  solve ")(" = 2 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve ")("

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve "(((())"

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve "((("
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible