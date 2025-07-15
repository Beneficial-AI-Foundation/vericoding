import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Int → Int → Int)
(x: Int) (y: Int) :=
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (∀ i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
∃ result, implementation x y = result ∧
spec result

-- LLM HELPER
def findLargestEven (x: Int) (y: Int) : Int :=
  if x > y then -1
  else if x = y ∧ Odd x then -1
  else if Even y then y
  else y - 1

def implementation (x: Int) (y: Int) : Int := findLargestEven x y

-- LLM HELPER
lemma even_or_odd (n : Int) : Even n ∨ Odd n := by
  cases' Int.even_or_odd n with h h
  · left; exact h
  · right; exact h

-- LLM HELPER
lemma odd_iff_not_even (n : Int) : Odd n ↔ ¬Even n := by
  exact Int.not_even_iff_odd.symm

-- LLM HELPER
lemma even_sub_one_of_odd (n : Int) : Odd n → Even (n - 1) := by
  intro h
  rw [Int.even_sub_odd]
  exact ⟨h, Int.odd_one⟩

-- LLM HELPER
lemma beq_eq_true_iff (a b : Int) : (a == b) = true ↔ a = b := by
  constructor
  · intro h
    exact Int.eq_of_beq_eq_true h
  · intro h
    simp [h]

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y := by
  unfold problem_spec implementation findLargestEven
  split_ifs with h1 h2 h3
  · -- Case: x > y
    use -1
    constructor
    · rfl
    constructor
    · left; rfl
    constructor
    · left; rfl
    · constructor
      · intro; rfl
      · intro; left; exact h1
  · -- Case: x = y ∧ Odd x
    use -1
    constructor
    · rfl
    constructor
    · left; rfl
    constructor
    · left; rfl
    · constructor
      · intro; rfl
      · intro
        right
        constructor
        · simp only [beq_eq_true_iff]
          exact h2.1
        · exact ⟨h2.2, h2.2⟩
  · -- Case: x ≤ y ∧ Even y
    use y
    constructor
    · rfl
    constructor
    · right
      constructor
      · exact le_of_not_gt h1
      constructor
      · rfl
      · exact h3
    constructor
    · right
      intros i h_i
      exact h_i.2.1
    · constructor
      · intro h_neg_one
        injection h_neg_one
      · intro h_cases
        cases' h_cases with h_gt h_eq_odd
        · exact absurd h_gt (not_lt.mpr (le_of_not_gt h1))
        · push_neg at h2
          rw [beq_eq_true_iff] at h_eq_odd
          cases' h2 (le_antisymm (le_of_not_gt h1) (le_of_eq h_eq_odd.1)) with h_not_eq h_not_odd
          · exact absurd h_eq_odd.1 (Ne.symm h_not_eq)
          · exact absurd h_eq_odd.2.1 h_not_odd
  · -- Case: x ≤ y ∧ Odd y
    use y - 1
    constructor
    · rfl
    constructor
    · right
      constructor
      · cases' Int.even_or_odd x with h_x_even h_x_odd
        · by_cases h_eq : x = y
          · rw [h_eq] at h_x_even
            push_neg at h3
            exact absurd h_x_even (odd_iff_not_even.mp h3)
          · exact Int.le_sub_one_of_lt (lt_of_le_of_ne (le_of_not_gt h1) h_eq)
        · by_cases h_eq : x = y
          · push_neg at h2
            cases' h2 h_eq with h_false h_not_odd
            · exact absurd h_eq h_false
            · rw [h_eq] at h_x_odd
              exact absurd h_x_odd h_not_odd
          · exact Int.le_sub_one_of_lt (lt_of_le_of_ne (le_of_not_gt h1) h_eq)
      constructor
      · exact Int.sub_one_le _
      · push_neg at h3
        exact even_sub_one_of_odd h3
    constructor
    · right
      intros i h_i
      have h_i_lt_y : i < y := by
        by_contra h_not_lt
        push_neg at h_not_lt
        have h_i_eq_y : i = y := le_antisymm h_i.2.1 h_not_lt
        rw [h_i_eq_y] at h_i
        push_neg at h3
        exact odd_iff_not_even.mp h3 h_i.2.2
      exact Int.le_sub_one_of_lt h_i_lt_y
    · constructor
      · intro h_neg_one
        injection h_neg_one
      · intro h_cases
        cases' h_cases with h_gt h_eq_odd
        · exact absurd h_gt (not_lt.mpr (le_of_not_gt h1))
        · push_neg at h2
          rw [beq_eq_true_iff] at h_eq_odd
          cases' h2 (le_antisymm (le_of_not_gt h1) (le_of_eq h_eq_odd.1)) with h_not_eq h_not_odd
          · exact absurd h_eq_odd.1 (Ne.symm h_not_eq)
          · exact absurd h_eq_odd.2.1 h_not_odd