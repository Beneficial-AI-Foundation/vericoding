def dollar_to_speech (s : String) : String := sorry

def String.containsStr (s₁ s₂ : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def formatDollarString (d c : Nat) : String :=
  s!"${d}.{c}"

theorem dollar_to_speech_ends_with_period (d c : Nat) (h : c < 100) :
  (dollar_to_speech (formatDollarString d c)).endsWith "." := sorry

theorem dollar_to_speech_single_dollar (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : d = 1) :
  (dollar_to_speech s).containsStr "1 dollar" ∧
  ¬(dollar_to_speech s).containsStr "dollars" := sorry

theorem dollar_to_speech_multiple_dollars (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : d > 1) :
  (dollar_to_speech s).containsStr s!"{d} dollars" := sorry

theorem dollar_to_speech_single_cent (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : c = 1) :
  (dollar_to_speech s).containsStr "1 cent" ∧
  ¬(dollar_to_speech s).containsStr "cents" := sorry

theorem dollar_to_speech_multiple_cents (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : c > 1) :
  (dollar_to_speech s).containsStr s!"{c} cents" := sorry

theorem dollar_to_speech_and_connector (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) :
  (d > 0 ∧ c > 0) ↔ (dollar_to_speech s).containsStr " and " := sorry

/-
info: '0 dollars.'
-/
-- #guard_msgs in
-- #eval dollar_to_speech "$0.00"

/-
info: '1 dollar.'
-/
-- #guard_msgs in
-- #eval dollar_to_speech "$1.00"

/-
info: '20 dollars and 18 cents.'
-/
-- #guard_msgs in
-- #eval dollar_to_speech "$20.18"

/-
info: 'No negative numbers are allowed!'
-/
-- #guard_msgs in
-- #eval dollar_to_speech "$-5.00"

-- Apps difficulty: introductory
-- Assurance level: unguarded