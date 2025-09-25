-- <vc-preamble>
def formatDollarString (d c : Nat) : String :=
  s!"${d}.{c}"
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def String.containsStr (s₁ s₂ : String) : Bool := sorry

def dollar_to_speech (s : String) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem dollar_to_speech_ends_with_period (d c : Nat) (h : c < 100) :
  (dollar_to_speech (formatDollarString d c)).endsWith "." :=
sorry

theorem dollar_to_speech_single_dollar (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : d = 1) :
  (dollar_to_speech s).containsStr "1 dollar" ∧
  ¬(dollar_to_speech s).containsStr "dollars" :=
sorry

theorem dollar_to_speech_multiple_dollars (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : d > 1) :
  (dollar_to_speech s).containsStr s!"{d} dollars" :=
sorry

theorem dollar_to_speech_single_cent (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : c = 1) :
  (dollar_to_speech s).containsStr "1 cent" ∧
  ¬(dollar_to_speech s).containsStr "cents" :=
sorry

theorem dollar_to_speech_multiple_cents (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) (h₂ : c > 1) :
  (dollar_to_speech s).containsStr s!"{c} cents" :=
sorry

theorem dollar_to_speech_and_connector (d c : Nat) (h : c < 100)
    (s := formatDollarString d c) :
  (d > 0 ∧ c > 0) ↔ (dollar_to_speech s).containsStr " and " :=
sorry
-- </vc-theorems>