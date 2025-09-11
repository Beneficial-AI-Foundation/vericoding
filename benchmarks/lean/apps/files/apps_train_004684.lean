-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_uppercase (s : String) : Bool := sorry

theorem empty_or_no_letters_is_true (s : String) :
  (∀ c ∈ s.data, !c.isAlpha) → is_uppercase s := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_uppercase_is_true (s : String) :
  (∀ c ∈ s.data, c.isUpper) → is_uppercase s := sorry

theorem any_lowercase_is_false (s : String) :
  s ≠ "" → (∃ c ∈ s.data, c.isLower) → ¬(is_uppercase s) := sorry

theorem mixed_case_rule (s : String) :
  is_uppercase s = ¬(∃ c ∈ s.data, c.isLower) := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_uppercase "c"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_uppercase "C"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_uppercase "hello I AM DONALD"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_uppercase "HELLO I AM DONALD"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_uppercase "ACSKLDFJSgSKLDFJSKLDFJ"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_uppercase "ACSKLDFJSGSKLDFJSKLDFJ"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_uppercase "123 !@#"
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded