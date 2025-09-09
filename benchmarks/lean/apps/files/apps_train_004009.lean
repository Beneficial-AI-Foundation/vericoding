-- <vc-helpers>
-- </vc-helpers>

def palindrome (n : Int) : Int :=
  sorry

theorem palindrome_outputs_int {x : Int} (h : x ≥ 0) :
  ∃ y : Int, palindrome x = y :=
  sorry

theorem palindrome_negative_rejects (x : Int) (h : x < 0) :
  palindrome x = -1 := -- assuming -1 represents 'Not valid'
  sorry

theorem palindrome_single_digit {x : Int} (h1 : x ≥ 0) (h2 : x ≤ 9) :
  palindrome x = 0 :=
  sorry

theorem palindrome_output_non_negative {x : Int} (h : x ≥ 0) :
  palindrome x ≥ 0 :=
  sorry

theorem palindrome_detects_basic {x : Int} (h : x = 1221) :
  palindrome x > 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval palindrome 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval palindrome 141221001

/-
info: 'Not valid'
-/
-- #guard_msgs in
-- #eval palindrome "1551"

-- Apps difficulty: introductory
-- Assurance level: unguarded