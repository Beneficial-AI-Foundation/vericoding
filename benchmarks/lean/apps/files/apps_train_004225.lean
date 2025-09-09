-- <vc-helpers>
-- </vc-helpers>

def timeCorrect (s : Option String) : Option String := sorry

def isValidTimeFormat (s : String) : Bool := sorry

theorem invalid_input_returns_none_or_same
  (s : Option String) : 
  s.isNone ∨ (s = some "") → timeCorrect s = s := sorry

theorem invalid_format_returns_none
  (s : String) :
  ¬isValidTimeFormat s → timeCorrect (some s) = none := sorry

theorem output_format_hours
  (s : String) :
  isValidTimeFormat s →
  ∀ t, timeCorrect (some s) = some t →
  ∃ (h : Nat), h < 24 ∧ t.take 2 = toString h := sorry

theorem output_format_minutes
  (s : String) :
  isValidTimeFormat s →
  ∀ t, timeCorrect (some s) = some t →
  ∃ (m : Nat), m < 60 ∧ String.drop (String.take t 5) 3 = toString m := sorry

theorem output_format_seconds
  (s : String) :
  isValidTimeFormat s →
  ∀ t, timeCorrect (some s) = some t →
  ∃ (s' : Nat), s' < 60 ∧ String.drop t 6 = toString s' := sorry

theorem output_format_length
  (s : String) :
  isValidTimeFormat s →
  ∀ t, timeCorrect (some s) = some t →
  t.length = 8 := sorry

theorem output_format_colons
  (s : String) :
  isValidTimeFormat s →
  ∀ t, timeCorrect (some s) = some t →
  t.data.get! 2 = ':' ∧ t.data.get! 5 = ':' := sorry

/-
info: '09:10:01'
-/
-- #guard_msgs in
-- #eval time_correct "09:10:01"

/-
info: '20:40:39'
-/
-- #guard_msgs in
-- #eval time_correct "19:99:99"

/-
info: '00:01:01'
-/
-- #guard_msgs in
-- #eval time_correct "24:01:01"

-- Apps difficulty: introductory
-- Assurance level: unguarded