-- <vc-preamble>
def min_parens_to_add (s : String) : Nat := sorry

def is_balanced (s : String) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_char (s : String) (c : Char) : Nat := sorry

theorem empty_string : min_parens_to_add "" = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem unmatched_open (n : Nat) :
  min_parens_to_add (String.mk (List.replicate n '(')) = n := sorry

theorem unmatched_close (n : Nat) :
  min_parens_to_add (String.mk (List.replicate n ')')) = n := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_parens_to_add "())"

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_parens_to_add "((("

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_parens_to_add "()"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible