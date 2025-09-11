-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def justify (text: String) (width : Nat) : String := sorry

-- Property 2: Input words are preserved in order
-- </vc-definitions>

-- <vc-theorems>
theorem justify_preserves_words (text: String) (width: Nat) (h: width ≥ 10):
  text ≠ "" →
  let input_words := (text.split (· = ' ')).filter (· ≠ "")
  let output_text := justify text width
  let output_words := (output_text.split (· = ' ')).filter (· ≠ "")
  input_words = output_words := sorry

-- Property 3: Empty input returns empty output  

theorem justify_empty (width: Nat):
  justify "" width = "" := sorry

-- Edge cases

theorem justify_edge_cases:
  (justify "" 5 = "") ∧
  (justify "a" 1 = "a") ∧ 
  (justify "a b" 3 = "a b") := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval justify "123 45 6" 7

/-
info: expected2
-/
-- #guard_msgs in
-- #eval justify "test" 10

/-
info: expected3
-/
-- #guard_msgs in
-- #eval justify "123 456" 10
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded