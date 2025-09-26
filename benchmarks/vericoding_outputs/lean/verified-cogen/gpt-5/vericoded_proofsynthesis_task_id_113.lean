import Mathlib
-- <vc-preamble>
/- Specification function to check if a character is a digit -/
def isDigitSpec (c : Char) : Bool :=
  c.toNat >= 48 ∧ c.toNat <= 57

@[reducible, simp]
def isInteger_precond (text : Array Char) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
instance : Coe Bool Prop where
  coe b := b = true

-- LLM HELPER
@[simp] theorem decide_true_iff (p : Prop) [Decidable p] : (decide p = true) ↔ p := by
  by_cases h : p
  · simp [h]
  · simp [h]

-- </vc-helpers>

-- <vc-definitions>
def isInteger (text : Array Char) (h_precond : isInteger_precond text) : Bool :=
  by
  classical
  exact decide (∀ i, i < text.size → isDigitSpec text[i]!)
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def isInteger_postcond (text : Array Char) (result: Bool) (h_precond : isInteger_precond text) : Prop :=
  (∀ i, i < text.size → isDigitSpec text[i]!) ↔ result

theorem isInteger_spec_satisfied (text: Array Char) (h_precond : isInteger_precond text) :
    isInteger_postcond text (isInteger text h_precond) h_precond := by
  classical
unfold isInteger_postcond isInteger
change (∀ i, i < text.size → isDigitSpec text[i]!) ↔ (decide (∀ i, i < text.size → isDigitSpec text[i]!) = true)
simpa using (Iff.symm (decide_true_iff (∀ i, i < text.size → isDigitSpec text[i]!)))
-- </vc-theorems>
