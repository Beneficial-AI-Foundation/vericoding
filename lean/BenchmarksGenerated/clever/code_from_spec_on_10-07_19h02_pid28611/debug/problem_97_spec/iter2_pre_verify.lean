import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result : Int) :=
  |result| ≤ 81 ∧
  result % 10 = (a * b) % 10 ∧
  ((b%10) ≠ 0 → (result % (b%10) = 0 ∧ (result/ (b%10)) % 100 = (a%10))) ∧
  ((a%10) ≠ 0 → (result % (a%10) = 0 ∧ (result/ (a%10)) % 100 = (b%10))) ∧
  ((a%10 = 0) ∨ (b%10 = 0) → result = 0)
-- program termination
∃ result,
  implementation a b = result ∧
  spec result

def implementation (a b: Int) : Int := 
  if (a % 10 = 0) ∨ (b % 10 = 0) then 0
  else (a % 10) * (b % 10)

-- LLM HELPER
lemma abs_le_81 (a b : Int) : |((a % 10) * (b % 10))| ≤ 81 := by
  have h1 : |a % 10| ≤ 9 := Int.abs_mod_two_div_two_le_iff.mp (Int.abs_mod_lt a (by norm_num : (10 : Int) ≠ 0))
  have h2 : |b % 10| ≤ 9 := Int.abs_mod_two_div_two_le_iff.mp (Int.abs_mod_lt b (by norm_num : (10 : Int) ≠ 0))
  have h3 : |(a % 10) * (b % 10)| = |a % 10| * |b % 10| := abs_mul (a % 10) (b % 10)
  rw [h3]
  have : |a % 10| ≤ 9 := by
    have : |a % 10| < 10 := Int.abs_mod_lt a (by norm_num : (10 : Int) ≠ 0)
    linarith
  have : |b % 10| ≤ 9 := by
    have : |b % 10| < 10 := Int.abs_mod_lt b (by norm_num : (10 : Int) ≠ 0)
    linarith
  have : |a % 10| * |b % 10| ≤ 9 * 9 := by
    apply Int.mul_le_mul_of_nonneg_of_nonneg
    · exact abs_nonneg _
    · exact abs_nonneg _
    · assumption
    · assumption
  calc |a % 10| * |b % 10| ≤ 9 * 9 := this
  _ = 81 := by norm_num

-- LLM HELPER
lemma mod_10_eq (a b : Int) : ((a % 10) * (b % 10)) % 10 = (a * b) % 10 := by
  rw [← Int.mul_emod, Int.mod_mod_of_dvd, Int.mod_mod_of_dvd]
  <;> norm_num

-- LLM HELPER
lemma div_mod_property (a b : Int) (ha : a % 10 ≠ 0) (hb : b % 10 ≠ 0) : 
  ((a % 10) * (b % 10)) % (b % 10) = 0 ∧ 
  ((a % 10) * (b % 10)) / (b % 10) % 100 = (a % 10) := by
  constructor
  · rw [Int.mul_emod, Int.mod_self, Int.mul_zero, Int.zero_mod]
  · rw [Int.mul_ediv_cancel_left (b % 10) ha]
    have : |a % 10| < 100 := by
      have : |a % 10| < 10 := Int.abs_mod_lt a (by norm_num : (10 : Int) ≠ 0)
      linarith
    exact Int.mod_eq_of_lt (Int.abs_lt.mp this).1 (Int.abs_lt.mp this).2

-- LLM HELPER
lemma div_mod_property' (a b : Int) (ha : a % 10 ≠ 0) (hb : b % 10 ≠ 0) : 
  ((a % 10) * (b % 10)) % (a % 10) = 0 ∧ 
  ((a % 10) * (b % 10)) / (a % 10) % 100 = (b % 10) := by
  constructor
  · rw [Int.mul_emod, Int.mod_self, Int.zero_mul, Int.zero_mod]
  · rw [Int.mul_ediv_cancel (a % 10) hb]
    have : |b % 10| < 100 := by
      have : |b % 10| < 10 := Int.abs_mod_lt b (by norm_num : (10 : Int) ≠ 0)
      linarith
    exact Int.mod_eq_of_lt (Int.abs_lt.mp this).1 (Int.abs_lt.mp this).2

theorem correctness
(a b: Int)
: problem_spec implementation a b
:= by
  unfold problem_spec implementation
  use (if (a % 10 = 0) ∨ (b % 10 = 0) then 0 else (a % 10) * (b % 10))
  constructor
  · rfl
  · by_cases h : (a % 10 = 0) ∨ (b % 10 = 0)
    · simp [h]
      constructor
      · norm_num
      · constructor
        · rw [Int.zero_mod]
          cases h with
          | inl ha => 
            rw [← Int.mul_emod]
            rw [ha, Int.zero_mul, Int.zero_mod]
          | inr hb => 
            rw [← Int.mul_emod]
            rw [hb, Int.mul_zero, Int.zero_mod]
        · constructor
          · intro hb_ne_zero
            push_neg at h
            cases h with
            | inl ha => contradiction
            | inr hb => contradiction
          · constructor
            · intro ha_ne_zero
              push_neg at h
              cases h with
              | inl ha => contradiction
              | inr hb => contradiction
            · intro; rfl
    · simp [h]
      push_neg at h
      cases h with
      | mk ha hb =>
        constructor
        · exact abs_le_81 a b
        · constructor
          · exact mod_10_eq a b
          · constructor
            · intro hb_ne_zero
              exact div_mod_property a b ha hb_ne_zero
            · constructor
              · intro ha_ne_zero
                exact div_mod_property' a b ha_ne_zero hb
              · intro h_contra
                cases h_contra with
                | inl ha_zero => contradiction
                | inr hb_zero => contradiction