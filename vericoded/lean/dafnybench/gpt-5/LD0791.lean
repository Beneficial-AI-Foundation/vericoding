import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem decide_of_true {p : Prop} [Decidable p] (hp : p) : decide p = true := by
  by_cases h : p
  · simpa [h]
  · exact (h hp).elim

-- LLM HELPER
theorem decide_eq_true_iff' (p : Prop) [Decidable p] : decide p = true ↔ p :=
  ⟨of_decide_eq_true, decide_of_true⟩
-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
decide (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11)
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
by
  intro _hRange
  apply propext
  change decide (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) = true ↔ (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11)
  simpa using decide_eq_true_iff' (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11)
-- </vc-theorems>
