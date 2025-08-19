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
def find_max_even (x: Int) (y: Int) : Int :=
  if x > y then -1
  else if x = y ∧ x % 2 = 1 then -1
  else if y % 2 = 0 then y
  else y - 1

def implementation (x: Int) (y: Int) : Int := find_max_even x y

-- LLM HELPER
lemma even_iff_mod_two_eq_zero (n : Int) : Even n ↔ n % 2 = 0 := by
  constructor
  · intro h
    cases' h with k hk
    rw [hk]
    simp only [Int.add_mul_emod_self_left, Int.zero_emod]
  · intro h
    use n / 2
    rw [← Int.emod_add_ediv n 2]
    rw [h]
    simp

-- LLM HELPER
lemma odd_iff_mod_two_eq_one (n : Int) : Odd n ↔ n % 2 = 1 := by
  constructor
  · intro h
    cases' h with k hk
    rw [hk]
    simp only [Int.add_mul_emod_self_left, Int.one_emod]
    norm_num
  · intro h
    use (n - 1) / 2
    rw [← Int.emod_add_ediv n 2]
    rw [h]
    ring

-- LLM HELPER
lemma int_even_or_odd (n : Int) : Even n ∨ Odd n := by
  by_cases h : n % 2 = 0
  · left
    rw [even_iff_mod_two_eq_zero]
    exact h
  · right
    rw [odd_iff_mod_two_eq_one]
    have : n % 2 = 0 ∨ n % 2 = 1 := by
      have : n % 2 ≥ 0 := Int.emod_nonneg n (by norm_num : (2 : Int) ≠ 0)
      have : n % 2 < 2 := Int.emod_lt_of_pos n (by norm_num : (0 : Int) < 2)
      have : n % 2 = 0 ∨ n % 2 = 1 := by
        have h1 : n % 2 ≥ 0 := this
        have h2 : n % 2 < 2 := this
        cases' Int.lt_iff_le_and_ne.mp h2 with h3 h4
        cases' le_iff_lt_or_eq.mp h3 with h5 h6
        · cases' Int.lt_iff_le_and_ne.mp h5 with h7 h8
          cases' le_iff_lt_or_eq.mp h7 with h9 h10
          · have : n % 2 < 0 := h9
            have : n % 2 ≥ 0 := h1
            linarith
          · left
            exact h10
        · right
          exact h6
      exact this
    cases this with
    | inl h0 => contradiction
    | inr h1 => exact h1

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y := by
  simp [problem_spec, implementation, find_max_even]
  let result := find_max_even x y
  use result
  constructor
  · rfl
  · simp [result, find_max_even]
    constructor
    · -- First condition: result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)
      by_cases h1 : x > y
      · simp [h1]
      · simp [h1]
        by_cases h2 : x = y ∧ x % 2 = 1
        · simp [h2]
        · simp [h2]
          push_neg at h1
          constructor
          · -- x ≤ result
            by_cases hy : y % 2 = 0
            · simp [hy]
              exact h1
            · simp [hy]
              have : x ≤ y - 1 := by
                by_cases hxy : x = y
                · rw [hxy]
                  linarith
                · have : x < y := by
                    cases' le_iff_lt_or_eq.mp h1 with h h
                    · exact h
                    · contradiction
                  linarith
              exact this
          constructor
          · -- result ≤ y
            by_cases hy : y % 2 = 0
            · simp [hy]
            · simp [hy]
              linarith
          · -- Even result
            by_cases hy : y % 2 = 0
            · simp [hy]
              rw [even_iff_mod_two_eq_zero]
              exact hy
            · simp [hy]
              rw [even_iff_mod_two_eq_zero]
              have : (y - 1) % 2 = 0 := by
                have : y % 2 = 1 := by
                  have : y % 2 = 0 ∨ y % 2 = 1 := by
                    have : y % 2 ≥ 0 := Int.emod_nonneg y (by norm_num : (2 : Int) ≠ 0)
                    have : y % 2 < 2 := Int.emod_lt_of_pos y (by norm_num : (0 : Int) < 2)
                    have h1 : y % 2 ≥ 0 := this
                    have h2 : y % 2 < 2 := this
                    cases' Int.lt_iff_le_and_ne.mp h2 with h3 h4
                    cases' le_iff_lt_or_eq.mp h3 with h5 h6
                    · cases' Int.lt_iff_le_and_ne.mp h5 with h7 h8
                      cases' le_iff_lt_or_eq.mp h7 with h9 h10
                      · have : y % 2 < 0 := h9
                        have : y % 2 ≥ 0 := h1
                        linarith
                      · left
                        exact h10
                    · right
                      exact h6
                  cases this with
                  | inl h => contradiction
                  | inr h => exact h
                have : (y - 1) % 2 = (y % 2 - 1 % 2) % 2 := by
                  rw [← Int.sub_emod]
                rw [this]
                norm_num
              exact this
    constructor
    · -- Second condition: result = -1 ∨ (∀ i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)
      by_cases h1 : x > y
      · simp [h1]
      · simp [h1]
        by_cases h2 : x = y ∧ x % 2 = 1
        · simp [h2]
        · simp [h2]
          push_neg at h1
          intro i hi_ge hi_le hi_even
          by_cases hy : y % 2 = 0
          · simp [hy]
            exact hi_le
          · simp [hy]
            have : i ≤ y - 1 := by
              by_contra h_not
              simp at h_not
              have : y ≤ i := by linarith
              have : i = y := le_antisymm hi_le this
              rw [this] at hi_even
              rw [even_iff_mod_two_eq_zero] at hi_even
              exact hy hi_even
            exact this
    · -- Third condition: result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y))
      constructor
      · -- Forward direction
        intro h_result
        by_cases h1 : x > y
        · left
          exact h1
        · simp [h1] at h_result
          by_cases h2 : x = y ∧ x % 2 = 1
          · right
            obtain ⟨hxy, hx_odd⟩ := h2
            constructor
            · simp [hxy]
            constructor
            · rw [odd_iff_mod_two_eq_one]
              exact hx_odd
            · rw [odd_iff_mod_two_eq_one]
              rw [← hxy]
              exact hx_odd
          · simp [h2] at h_result
      · -- Backward direction
        intro h_cond
        cases h_cond with
        | inl h => simp [h]
        | inr h => 
          obtain ⟨hxy, hx_odd, hy_odd⟩ := h
          simp [le_of_not_gt (not_lt.mpr (le_of_eq hxy))]
          simp [hxy]
          rw [odd_iff_mod_two_eq_one] at hx_odd
          simp [hx_odd]