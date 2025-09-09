/-
Write function RemoveExclamationMarks which removes all exclamation marks from a given string.
-/

def countChars (s : String) (c : Char) : Nat := 
  sorry

-- <vc-helpers>
-- </vc-helpers>

def remove_exclamation_marks (s : String) : String :=
  sorry

theorem no_exclamation_in_result (s : String) :
  ¬(remove_exclamation_marks s).contains '!' := by sorry

theorem length_after_removal (s : String) :
  (remove_exclamation_marks s).length = s.length - (countChars s '!') := by sorry

theorem result_equals_remove_exclamation (s : String) :
  (remove_exclamation_marks s).replace "!" "" = remove_exclamation_marks s := by sorry

theorem unchanged_without_exclamation (s : String) (h : ¬s.contains '!') :
  remove_exclamation_marks s = s := by sorry

theorem concatenation_property (s₁ s₂ : String) :
  remove_exclamation_marks s₁ ++ remove_exclamation_marks s₂ = 
  remove_exclamation_marks (s₁ ++ s₂) := by sorry

/-
info: 'Hello World'
-/
-- #guard_msgs in
-- #eval remove_exclamation_marks "Hello World!"

/-
info: 'Hi Hello'
-/
-- #guard_msgs in
-- #eval remove_exclamation_marks "Hi! Hello!"

/-
info: 'Oh, no'
-/
-- #guard_msgs in
-- #eval remove_exclamation_marks "Oh, no!!!"

-- Apps difficulty: introductory
-- Assurance level: unguarded