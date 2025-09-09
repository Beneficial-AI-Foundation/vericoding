/-
Complete the `greatestProduct` method so that it'll find the greatest product of five consecutive digits in the given string of digits.

For example:

The input string always has more than five digits.

Adapted from Project Euler.
-/

-- <vc-helpers>
-- </vc-helpers>

def greatest_product (s : String) : Nat := sorry

def digit_product (s : String) : Nat := sorry

theorem zero_gives_zero_window {s : String} (h : s.length ≥ 5) :
  let with_zero := s.take 3 ++ "0" ++ s.drop 3
  if with_zero.contains '0' then
    greatest_product with_zero = 0 ∨ ∃ d, d ∈ with_zero.data ∧ d.toNat > 0
  else True := sorry

/-
info: 3240
-/
-- #guard_msgs in
-- #eval greatest_product "123834539327238239583"

/-
info: 3240
-/
-- #guard_msgs in
-- #eval greatest_product "395831238345393272382"

/-
info: 5292
-/
-- #guard_msgs in
-- #eval greatest_product "92494737828244222221111111532909999"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible