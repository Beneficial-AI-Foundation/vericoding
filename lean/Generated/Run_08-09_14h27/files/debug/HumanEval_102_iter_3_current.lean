/- 
function_signature: "def choose_num(x: int, y: int) -> int"
docstring: |
    This function takes two positive numbers x and y and returns the
    biggest even integer number that is in the range [x, y] inclusive. If
    there's no such number, then the function should return -1.
test_cases:
  - input: (12, 15)
    expected_output: 14
  - input: (13, 12)
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: Int) (y: Int) : Int :=
  if x > y then -1
  else if Even y then y
  else if y - 1 >= x then y - 1
  else -1

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(x: Int) (y: Int) :=
-- spec
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (forall i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
-- program termination
∃ result, implementation x y = result ∧
spec result

-- LLM HELPER
lemma even_or_odd (n : Int) : Even n ∨ Odd n := by
  exact Int.even_or_odd n

-- LLM HELPER
lemma even_iff_not_odd (n : Int) : Even n ↔ ¬Odd n := by
  rw [Int.even_iff_not_odd]

-- LLM HELPER
lemma odd_iff_not_even (n : Int) : Odd n ↔ ¬Even n := by
  rw [Int.odd_iff_not_even]

-- LLM HELPER
lemma even_sub_odd (n : Int) : Odd n → Even (n - 1) := by
  intro h
  exact Int.even_sub_odd h

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y
:= by
  unfold problem_spec implementation
  use if x > y then -1 else if Even y then y else if y - 1 ≥ x then y - 1 else -1
  constructor
  · rfl
  · by_cases h1 : x > y
    · simp [h1]
      constructor
      · left; rfl
      · constructor
        · left; rfl
        · simp; exact h1
    · simp [h1]
      by_cases h2 : Even y
      · simp [h2]
        constructor
        · right
          constructor
          · exact Int.le_of_not_gt h1
          · constructor
            · le_refl
            · exact h2
        · constructor
          · right
            intro i hi
            exact hi.2.1
          · simp
            intro h
            exfalso
            cases h with
            | inl h_gt => exact h1 h_gt
            | inr h_case => 
              have : Odd y := odd_iff_not_even.mpr h2
              exact even_iff_not_odd.mp h2 this
      · simp [h2]
        by_cases h3 : y - 1 ≥ x
        · simp [h3]
          constructor
          · right
            constructor
            · exact h3
            · constructor
              · exact Int.sub_le y 1
              · have : Odd y := odd_iff_not_even.mpr h2
                exact even_sub_odd y this
          · constructor
            · right
              intro i hi
              have ile : i ≤ y := hi.2.1
              by_cases h4 : i = y
              · rw [h4] at hi
                exact absurd hi.2.2 h2
              · have : i < y := by
                  exact Int.lt_of_le_of_ne ile h4
                exact Int.le_sub_one_of_lt this
            · simp
              intro h
              cases h with
              | inl h_gt => exact h1 h_gt
              | inr h_case =>
                have y_odd : Odd y := odd_iff_not_even.mpr h2
                by_cases h_eq : x = y
                · have x_odd : Odd x := by rw [h_eq]; exact y_odd
                  exact h_case.2 ⟨h_eq, x_odd, y_odd⟩
                · have : x < y := Int.lt_of_le_of_ne (Int.le_of_not_gt h1) h_eq
                  have : x ≤ y - 1 := Int.le_sub_one_of_lt this
                  exact h3 this
        · simp [h3]
          constructor
          · left; rfl
          · constructor
            · left; rfl
            · simp
              right
              constructor
              · intro ⟨h_eq, hx_odd, hy_odd⟩
                rw [h_eq]
                have : ¬(y - 1 ≥ y) := by
                  simp
                  exact Int.lt_sub_one y
                exact this
              · intro h
                have y_odd : Odd y := odd_iff_not_even.mpr h2
                have : x ≤ y := Int.le_of_not_gt h1
                have : x = y := by
                  by_contra h_ne
                  have : x < y := Int.lt_of_le_of_ne this h_ne
                  have : x ≤ y - 1 := Int.le_sub_one_of_lt this
                  exact h3 this
                have x_odd : Odd x := by rw [this]; exact y_odd
                exact ⟨this, x_odd, y_odd⟩

-- #test implementation 12 15 = 14
-- #test implementation 13 12 = -1
-- #test implementation 33 12354 = 12354
-- #test implementation 5234 5233 = -1
-- #test implementation 6 29 = 28
-- #test implementation 27 10 = (-1)
-- #test implementation 7 7 = -1
-- #test implementation 546 546 = 546