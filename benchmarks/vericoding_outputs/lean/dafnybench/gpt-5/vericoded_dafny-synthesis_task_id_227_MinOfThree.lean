import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] theorem min_eq_left_or_right_int (x y : Int) : min x y = x ∨ min x y = y := by
  rcases le_total x y with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

-- </vc-helpers>

-- <vc-definitions>
def MinOfThree (a b c : Int) : Int :=
min (min a b) c
-- </vc-definitions>

-- <vc-theorems>
theorem MinOfThree_spec (a b c : Int) :
let min := MinOfThree a b c
min ≤ a ∧ min ≤ b ∧ min ≤ c ∧ (min = a ∨ min = b ∨ min = c) :=
by
  intro m
  have hm_le_minab : m ≤ min a b := by
    have h := min_le_left (min a b) c
    simpa [MinOfThree, m] using h
  have hm_le_c : m ≤ c := by
    have h := min_le_right (min a b) c
    simpa [MinOfThree, m] using h
  have hm_le_a : m ≤ a := le_trans hm_le_minab (min_le_left a b)
  have hm_le_b : m ≤ b := le_trans hm_le_minab (min_le_right a b)
  have h₁ : m = min a b ∨ m = c := by
    have h := min_eq_left_or_right_int (min a b) c
    simpa [MinOfThree, m] using h
  have h₂ : min a b = a ∨ min a b = b := min_eq_left_or_right_int a b
  refine And.intro hm_le_a (And.intro hm_le_b (And.intro hm_le_c ?_))
  cases h₁ with
  | inl hm_eq =>
    cases h₂ with
    | inl hma =>
      exact Or.inl (hm_eq.trans hma)
    | inr hmb =>
      exact Or.inr (Or.inl (hm_eq.trans hmb))
  | inr hmc =>
    exact Or.inr (Or.inr hmc)

-- </vc-theorems>
