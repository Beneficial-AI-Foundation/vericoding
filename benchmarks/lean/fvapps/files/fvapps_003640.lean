-- <vc-preamble>
def palin (length pos : Nat) : Nat := sorry

def is_palindrome (n : Nat) : Bool := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def num_length (n : Nat) : Nat := sorry

theorem single_digit_palindromes (pos : Nat) (h : 0 < pos ∧ pos < 10) : 
  let result := palin 1 pos
  result = pos ∧ result < 10 := sorry
-- </vc-definitions>

-- <vc-theorems>
/-
info: 22
-/
-- #guard_msgs in
-- #eval palin 2 2

/-
info: 1441
-/
-- #guard_msgs in
-- #eval palin 4 5

/-
info: 102201
-/
-- #guard_msgs in
-- #eval palin 6 3
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible