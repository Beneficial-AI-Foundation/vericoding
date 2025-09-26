import Mathlib
-- <vc-preamble>
@[reducible]
def maxOfThree_precond (a : Int) (b : Int) (c : Int) : Prop :=
  True
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
lemma int_max_eq_left_or_right (x y : Int) : max x y = x ∨ max x y = y := by
  cases le_total y x with
  | inl hyx =>
      exact Or.inl (by simpa using (max_eq_left hyx))
  | inr hxy =>
      exact Or.inr (by simpa using (max_eq_right hxy))
-- </vc-helpers>

-- <vc-definitions>
def maxOfThree (a : Int) (b : Int) (c : Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Int :=
  max a (max b c)
-- </vc-definitions>

-- <vc-theorems>
@[reducible]
def maxOfThree_postcond (a : Int) (b : Int) (c : Int) (result: Int) (h_precond : maxOfThree_precond (a) (b) (c)) : Prop :=
  (result >= a ∧ result >= b ∧ result >= c) ∧ (result = a ∨ result = b ∨ result = c)

theorem maxOfThree_spec_satisfied (a: Int) (b: Int) (c: Int) (h_precond : maxOfThree_precond (a) (b) (c)) :
    maxOfThree_postcond (a) (b) (c) (maxOfThree (a) (b) (c) h_precond) h_precond := by
  unfold maxOfThree
  let r := max a (max b c)
  have ha : r ≥ a := by
    have : a ≤ r := by simpa [r] using le_max_left a (max b c)
    simpa [r] using this
  have h_mbc_le_r : max b c ≤ r := by
    simpa [r] using (le_max_right a (max b c))
  have hb : r ≥ b := by
    have : b ≤ r := le_trans (le_max_left b c) h_mbc_le_r
    simpa [r] using this
  have hc : r ≥ c := by
    have : c ≤ r := le_trans (le_max_right b c) h_mbc_le_r
    simpa [r] using this
  have hr_eq : r = a ∨ r = b ∨ r = c := by
    cases le_total (max b c) a with
    | inl hle =>
        have hr_eq_a : r = a := by
          simpa [r] using (max_eq_left hle)
        exact Or.inl hr_eq_a
    | inr hge =>
        have hr_eq_m : r = max b c := by
          simpa [r] using (max_eq_right hge)
        cases le_total c b with
        | inl hclb =>
            have : r = b := by
              have : max b c = b := by simpa using (max_eq_left hclb)
              simpa [hr_eq_m, this]
            exact Or.inr (Or.inl this)
        | inr hblc =>
            have : r = c := by
              have : max b c = c := by simpa using (max_eq_right hblc)
              simpa [hr_eq_m, this]
            exact Or.inr (Or.inr this)
  refine And.intro ?_ ?_
  · exact And.intro ha (And.intro hb hc)
  · simpa [r] using hr_eq
-- </vc-theorems>

/-
-- Invalid Inputs
[]
-- Tests
[
    {
        "input": {
            "a": 3,
            "b": 2,
            "c": 1
        },
        "expected": 3,
        "unexpected": [
            2,
            1,
            -1
        ]
    },
    {
        "input": {
            "a": 5,
            "b": 5,
            "c": 5
        },
        "expected": 5,
        "unexpected": [
            6,
            4
        ]
    },
    {
        "input": {
            "a": 10,
            "b": 20,
            "c": 15
        },
        "expected": 20,
        "unexpected": [
            10,
            15
        ]
    },
    {
        "input": {
            "a": -1,
            "b": -2,
            "c": -3
        },
        "expected": -1,
        "unexpected": [
            -2,
            -3
        ]
    },
    {
        "input": {
            "a": 0,
            "b": -10,
            "c": -5
        },
        "expected": 0,
        "unexpected": [
            -5,
            -10
        ]
    }
]
-/