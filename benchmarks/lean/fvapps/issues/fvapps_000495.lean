-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def myAtoi (s : String) : Int := sorry

theorem myAtoi_within_bounds (s : String) :
  -2147483648 ≤ myAtoi s ∧ myAtoi s ≤ 2147483647 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem myAtoi_leading_whitespace (s : String) :
  myAtoi ("   " ++ s) = myAtoi s := sorry

theorem myAtoi_signs_positive (n : Int) 
  (h : 0 ≤ n ∧ n ≤ 2147483647) :
  myAtoi ("+" ++ toString n) = n := sorry

theorem myAtoi_signs_negative (n : Int)
  (h : 0 ≤ n ∧ n ≤ 2147483647) :
  myAtoi ("-" ++ toString n) = -min n 2147483648 := sorry

/-
info: 42
-/
-- #guard_msgs in
-- #eval myAtoi "42"

/-
info: -42
-/
-- #guard_msgs in
-- #eval myAtoi "   -42"

/-
info: 4193
-/
-- #guard_msgs in
-- #eval myAtoi "4193 with words"

/-
info: 0
-/
-- #guard_msgs in
-- #eval myAtoi "words and 987"

/-
info: -2147483648
-/
-- #guard_msgs in
-- #eval myAtoi "-91283472332"
-- </vc-theorems>