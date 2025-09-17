-- <vc-preamble>
def isLower (c : Char) : Bool :=
  sorry

def isUpper (c : Char) : Bool :=
  sorry

def isDigit (c : Char) : Bool :=
  sorry

def hasThreeRepeated (s : String) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def strongPasswordChecker (s : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_non_negative (s : String) :
  strongPasswordChecker s ≥ 0 :=
  sorry

theorem valid_password_needs_no_changes (s : String) :
  (s.length ≥ 6 ∧ s.length ≤ 20 ∧
   s.any isLower ∧
   s.any isUpper ∧
   s.any isDigit ∧
   ¬hasThreeRepeated s) →
  strongPasswordChecker s = 0 :=
  sorry

theorem short_password_minimum_changes (s : String) :
  s.length < 6 →
  strongPasswordChecker s ≥ 6 - s.length :=
  sorry

theorem long_password_minimum_changes (s : String) :
  s.length > 20 →
  strongPasswordChecker s ≥ s.length - 20 :=
  sorry

theorem missing_categories_minimum_changes (s : String) :
  let missing := (if s.any isLower then 0 else 1) +
                 (if s.any isUpper then 0 else 1) +
                 (if s.any isDigit then 0 else 1)
  strongPasswordChecker s ≥ missing :=
  sorry

theorem repeated_chars_minimum_changes (s : String) :
  (∀ c : Char, c ∈ s.data → c = 'a') →
  s.length ≥ 3 →
  strongPasswordChecker s ≥ s.length / 3 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval strongPasswordChecker "a"

/-
info: 3
-/
-- #guard_msgs in
-- #eval strongPasswordChecker "aA1"

/-
info: 0
-/
-- #guard_msgs in
-- #eval strongPasswordChecker "1337C0d3"
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded