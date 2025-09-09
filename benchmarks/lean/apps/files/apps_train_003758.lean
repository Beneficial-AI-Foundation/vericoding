-- <vc-helpers>
-- </vc-helpers>

def align_right (text : String) (width : Nat) : String := sorry

theorem width_equal_to_content (text : String) (line : String) : 
  line ≠ "" →
  line ∈ (text.split (· = '\n')) →
  align_right line (line.length) = line := sorry

theorem basic_properties_nonempty (text : String) (width : Nat) :
  text.trim ≠ "" →
  width ≥ 10 →
  (align_right text width).trim ≠ "" := sorry

theorem basic_properties_width (text : String) (width : Nat) : 
  text.trim ≠ "" →
  width ≥ 10 →
  ∀ line ∈ (align_right text width).split (· = '\n'), 
    line.length ≤ width := sorry

theorem basic_properties_alignment (text : String) (width : Nat) :
  text.trim ≠ "" →
  width ≥ 10 →
  ∀ line ∈ (align_right text width).split (· = '\n'),
    !line.startsWith line.trim ∨ line.trim = line := sorry

/-
info: expected
-/
-- #guard_msgs in
-- #eval align_right "abc def" 10

/-
info: expected
-/
-- #guard_msgs in
-- #eval align_right "I take up the whole line" 24

/-
info: expected
-/
-- #guard_msgs in
-- #eval align_right "Two lines, I am" 10

-- Apps difficulty: introductory
-- Assurance level: unguarded