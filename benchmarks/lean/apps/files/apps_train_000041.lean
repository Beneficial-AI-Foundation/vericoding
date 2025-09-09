-- <vc-helpers>
-- </vc-helpers>

def solve_bracket_sequence (n k : Nat) (s : String) : List (List Nat) := sorry

-- The minimal move for ")(" is [[1,2]]

theorem solve_bracket_minimal (n k : Nat) (s : String) :
  n = 2 → k = 1 → s = ")(" → 
  solve_bracket_sequence n k s = [[1,2]] := sorry

-- No moves needed for already correct sequence "()"

theorem solve_bracket_correct (n k : Nat) (s : String) :
  n = 2 → k = 1 → s = "()" →
  solve_bracket_sequence n k s = [] := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval len solve_bracket_sequence(n, k, s)

/-
info: 1
-/
-- #guard_msgs in
-- #eval len solve_bracket_sequence(n, k, s)

-- Apps difficulty: interview
-- Assurance level: unguarded