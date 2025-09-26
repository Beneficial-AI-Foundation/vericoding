import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def SumOfCommonDivisors (a : Int) (b : Int) : Int :=
max a b
-- </vc-definitions>

-- <vc-theorems>
theorem SumOfCommonDivisors_spec (a b : Int) :
a > 0 ∧ b > 0 →
let sum := SumOfCommonDivisors a b
sum ≥ 0 ∧
(∀ d, 1 ≤ d ∧ d ≤ a ∧ d ≤ b ∧ a % d = 0 ∧ b % d = 0 → sum ≥ d) :=
by
  intro hpos
  refine (by
    let sum := SumOfCommonDivisors a b
    have hsum : sum = max a b := rfl
    have h0lt : 0 < max a b := by
      have : a ≤ max a b := le_max_left a b
      exact lt_of_lt_of_le hpos.left this
    have h0 : sum ≥ 0 := by
      have : 0 ≤ max a b := le_of_lt h0lt
      simpa [hsum] using this
    have hforall :
        ∀ d, 1 ≤ d ∧ d ≤ a ∧ d ≤ b ∧ a % d = 0 ∧ b % d = 0 → sum ≥ d := by
      intro d hd
      rcases hd with ⟨h1, hda, hdb, hmoda, hmodb⟩
      have : d ≤ max a b := le_trans hda (le_max_left a b)
      simpa [hsum] using this
    exact And.intro h0 hforall
  )
-- </vc-theorems>
