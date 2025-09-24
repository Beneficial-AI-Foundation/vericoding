-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValid (s : String) : Bool := sorry

-- All strings consisting of letters/underscores/$ followed by letters/numbers/underscores/$ are valid
-- </vc-definitions>

-- <vc-theorems>
theorem valid_identifier (s : String)
  (h : s.data = x::xs ∧ (x = '_' ∨ x = '$' ∨ ('A' ≤ x ∧ x ≤ 'Z') ∨ ('a' ≤ x ∧ x ≤ 'z')) ∧ 
   ∀ c ∈ xs, (('0' ≤ c ∧ c ≤ '9') ∨ ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z') ∨ c = '_' ∨ c = '$')) :
  isValid s = true := sorry

-- Edge cases

theorem empty_invalid : isValid "" = false := sorry

theorem underscore_valid : isValid "_" = true := sorry

theorem dollar_valid : isValid "$" = true := sorry

theorem space_invalid : isValid " " = false := sorry

theorem leading_number_invalid : isValid "1abc" = false := sorry

theorem whitespace_invalid : isValid "abc def" = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_valid "okay_ok1"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_valid ""

/-
info: False
-/
-- #guard_msgs in
-- #eval is_valid "no no"
-- </vc-theorems>