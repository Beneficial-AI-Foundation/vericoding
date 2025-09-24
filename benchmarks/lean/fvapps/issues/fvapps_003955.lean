-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def no_repeat (s : String) : Option Char := sorry

/- If a string has any character that appears exactly once,
    then the result of no_repeat is a character from the string
    that appears exactly once -/
-- </vc-definitions>

-- <vc-theorems>
theorem no_repeat_in_string (s : String) (h : ∃ c, s.data.count c = 1) :
  let result := no_repeat s
  match result with
  | none => False
  | some c => c ∈ s.data ∧ s.data.count c = 1 := sorry

/- If a string has any character that appears exactly once,
    then no_repeat returns the first such character in the string -/

theorem no_repeat_first_single (s : String) (h : ∃ c, s.data.count c = 1) :
  let result := no_repeat s
  match result with
  | none => False
  | some c => ∀ c', c' ∈ s.data → s.data.count c' = 1 →
             s.data.indexOf c' ≥ s.data.indexOf c := sorry

/- If a string has no characters that appear exactly once,
    then no_repeat returns none -/

theorem no_repeat_no_singles (s : String) (h : ∀ c, c ∈ s.data → s.data.count c ≠ 1) :
  no_repeat s = none := sorry

/-
info: 'e'
-/
-- #guard_msgs in
-- #eval no_repeat "aabbccdde"

/-
info: 'w'
-/
-- #guard_msgs in
-- #eval no_repeat "wxyz"

/-
info: 'e'
-/
-- #guard_msgs in
-- #eval no_repeat "testing"
-- </vc-theorems>