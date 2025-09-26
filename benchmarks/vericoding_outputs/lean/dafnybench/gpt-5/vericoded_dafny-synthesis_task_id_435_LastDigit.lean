import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma ten_pos_int : (0 : Int) < 10 := by decide
lemma ten_ne_zero_int : (10 : Int) ≠ 0 := by decide
-- </vc-helpers>

-- <vc-definitions>
def LastDigit (n : Int) : Int :=
n % 10
-- </vc-definitions>

-- <vc-theorems>
theorem LastDigit_spec (n : Int) :
n ≥ 0 →
let d := LastDigit n
0 ≤ d ∧ d < 10 ∧ n % 10 = d :=
by
  intro _
  have h : 0 ≤ n % 10 ∧ n % 10 < 10 ∧ n % 10 = n % 10 := by
    refine And.intro ?_ ?_
    · exact Int.emod_nonneg _ (by decide)
    ·
      have : (0 : Int) < 10 := by decide
      exact And.intro (Int.emod_lt_of_pos _ this) rfl
  simpa [LastDigit] using h
-- </vc-theorems>
