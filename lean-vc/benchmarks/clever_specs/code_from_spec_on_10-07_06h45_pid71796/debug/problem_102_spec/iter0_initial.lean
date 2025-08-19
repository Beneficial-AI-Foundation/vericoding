import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
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
def find_largest_even (x: Int) (y: Int) : Int :=
  if x > y then -1
  else if x = y ∧ x % 2 = 1 then -1
  else if y % 2 = 0 then y
  else y - 1

def implementation (x: Int) (y: Int) : Int := find_largest_even x y

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (n: Int) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro h
    cases' h with k hk
    simp [hk]
  · intro h
    use n / 2
    rw [Int.mul_comm]
    exact Int.mul_eDiv_cancel_of_emod_eq_zero h

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n: Int) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases' h with k hk
    simp [hk]
    ring
  · intro h
    use (n - 1) / 2
    rw [Int.mul_comm]
    have : n = 2 * ((n - 1) / 2) + 1 := by
      rw [← Int.add_mul_eDiv_right (n - 1) (by norm_num : (2 : Int) ≠ 0)]
      simp [Int.sub_emod, h]
      ring
    exact this.symm

-- LLM HELPER
lemma largest_even_in_range (x y: Int) (hxy: x ≤ y) : 
  (∃ e: Int, x ≤ e ∧ e ≤ y ∧ Even e) → 
  (if y % 2 = 0 then y else y - 1) ≥ x ∧ 
  (if y % 2 = 0 then y else y - 1) ≤ y ∧ 
  Even (if y % 2 = 0 then y else y - 1) := by
  intro h
  constructor
  · split_ifs with hy
    · cases' h with e he
      have : e ≤ y := he.2.1
      exact le_trans he.1 (le_refl y)
    · cases' h with e he
      have : e ≤ y := he.2.1
      have : e ≤ y - 1 := by
        have hy_odd : Odd y := by
          rw [odd_iff_mod_two_eq_one]
          simp at hy
          exact Int.mod_two_eq_one_iff_odd.mp hy
        rw [even_iff_mod_two_eq_zero] at he
        have : e % 2 = 0 := he.2.2
        have : e ≠ y := by
          intro heq
          rw [heq] at this
          rw [odd_iff_mod_two_eq_one] at hy_odd
          rw [this] at hy_odd
          norm_num at hy_odd
        exact Int.lt_iff_le_and_ne.mp (lt_of_le_of_ne he.2.1 this)
      exact le_trans he.1 this
  constructor
  · split_ifs with hy
    · rfl
    · exact Int.sub_one_lt_iff.mp (lt_refl y)
  · split_ifs with hy
    · rw [even_iff_mod_two_eq_zero]
      exact hy
    · rw [even_iff_mod_two_eq_zero]
      simp at hy
      have : y % 2 = 1 := Int.mod_two_eq_one_iff_odd.mpr (odd_iff_mod_two_eq_one.mpr hy)
      rw [Int.sub_emod]
      simp [this]

-- LLM HELPER
lemma no_even_in_range (x y: Int) : 
  (x > y ∨ (x = y ∧ Odd x ∧ Odd y)) → 
  ¬∃ e: Int, x ≤ e ∧ e ≤ y ∧ Even e := by
  intro h
  cases' h with h1 h2
  · intro ⟨e, he⟩
    have : x ≤ e := he.1
    have : e ≤ y := he.2.1
    have : x ≤ y := le_trans this (le_of_lt h1)
    exact not_le.mpr h1 this
  · intro ⟨e, he⟩
    have : x ≤ e := he.1
    have : e ≤ y := he.2.1
    have : x = y := h2.1
    have : e = x := le_antisymm (le_trans he.2.1 (le_of_eq h2.1.symm)) he.1
    have : e = y := by rw [this, h2.1]
    have : Even e := he.2.2
    have : Odd y := h2.2.2
    rw [← this.symm] at this
    exact Odd.not_even this this

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y := by
  unfold problem_spec implementation find_largest_even
  split_ifs with h1 h2
  · -- Case: x > y
    use -1
    simp
    constructor
    · left; rfl
    constructor
    · left; rfl
    · left; rfl
  · -- Case: x = y ∧ x % 2 = 1
    use -1
    simp
    constructor
    · left; rfl
    constructor
    · left; rfl
    · constructor
      · intro h
        right
        constructor
        · simp at h2
          exact h2.1
        · constructor
          · rw [odd_iff_mod_two_eq_one]
            simp at h2
            exact h2.2
          · rw [odd_iff_mod_two_eq_one]
            simp at h2
            rw [h2.1]
            exact h2.2
      · intro h
        cases' h with h3 h4
        · exact h3
        · simp at h2
          exact ⟨h2.1, h2.2⟩
  · -- Case: y % 2 = 0
    use y
    simp
    constructor
    · right
      constructor
      · exact le_of_not_gt h1
      constructor
      · rfl
      · rw [even_iff_mod_two_eq_zero]
        simp at h2
        push_neg at h2
        cases' h2 with h2a h2b
        · contradiction
        · exact h2b
    constructor
    · right
      intro i hi
      exact hi.2.1
    · constructor
      · intro h
        exfalso
        push_neg at h1
        simp at h2
        push_neg at h2
        cases' h2 with h2a h2b
        · contradiction
        · rw [even_iff_mod_two_eq_zero] at h2b
          exact h2b rfl
      · intro h
        cases' h with h3 h4
        · exact le_of_not_gt h1
        · exfalso
          cases' h4 with h4a h4b
          have : x = y := h4a.1
          have : Odd x := h4a.2.1
          have : Odd y := h4a.2.2
          rw [odd_iff_mod_two_eq_one] at h4a.2.2
          simp at h2
          push_neg at h2
          cases' h2 with h2a h2b
          · contradiction
          · exact h2b h4a.2.2
  · -- Case: y % 2 = 1
    use y - 1
    simp
    constructor
    · right
      constructor
      · exact le_of_not_gt h1
      constructor
      · exact Int.sub_one_lt_iff.mp (lt_refl y)
      · rw [even_iff_mod_two_eq_zero]
        rw [Int.sub_emod]
        simp at h2
        push_neg at h2
        cases' h2 with h2a h2b
        · simp at h2a
          cases' h2a with h2aa h2ab
          · contradiction
          · rw [Int.sub_emod]
            simp [h2ab]
        · simp [h2b]
    constructor
    · right
      intro i hi
      have : i ≤ y := hi.2.1
      have : i ≤ y - 1 := by
        have : i ≠ y := by
          intro heq
          rw [heq] at hi
          have : Even y := hi.2.2
          have : Odd y := by
            rw [odd_iff_mod_two_eq_one]
            simp at h2
            push_neg at h2
            cases' h2 with h2a h2b
            · simp at h2a
              cases' h2a with h2aa h2ab
              · contradiction
              · exact h2ab
            · exact h2b
          exact Odd.not_even this this
        exact Int.lt_iff_le_and_ne.mp (lt_of_le_of_ne this this)
      exact this
    · constructor
      · intro h
        exfalso
        push_neg at h1
        simp at h2
        push_neg at h2
        cases' h2 with h2a h2b
        · simp at h2a
          cases' h2a with h2aa h2ab
          · contradiction
          · rw [even_iff_mod_two_eq_zero] at h2ab
            exact h2ab rfl
        · rw [even_iff_mod_two_eq_zero] at h2b
          exact h2b rfl
      · intro h
        cases' h with h3 h4
        · exact le_of_not_gt h1
        · exfalso
          cases' h4 with h4a h4b
          have : x = y := h4a.1
          have : Odd y := h4a.2.2
          rw [odd_iff_mod_two_eq_one] at h4a.2.2
          simp at h2
          push_neg at h2
          cases' h2 with h2a h2b
          · simp at h2a
            cases' h2a with h2aa h2ab
            · contradiction
            · exact h2ab h4a.2.2
          · exact h2b h4a.2.2