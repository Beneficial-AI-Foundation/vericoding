-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_bracket_sequence (n k : Nat) (s : String) : List (List Nat) := sorry

-- The minimal move for ")(" is [[1,2]]
-- </vc-definitions>

-- <vc-theorems>
theorem solve_bracket_minimal (n k : Nat) (s : String) :
  n = 2 → k = 1 → s = ")(" → 
  solve_bracket_sequence n k s = [[1,2]] := sorry

-- No moves needed for already correct sequence "()"

theorem solve_bracket_correct (n k : Nat) (s : String) :
  n = 2 → k = 1 → s = "()" →
  solve_bracket_sequence n k s = [] := sorry
-- </vc-theorems>