import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
0 < n → 0 < result → result ∣ n → ∀ x, x ∣ n → x ≠ n → x ≤ result;
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def max_proper_divisor (n: Nat) : Nat :=
if n ≤ 1 then 1
else
  let rec helper (k: Nat) : Nat :=
    if k = 1 then 1
    else if n % k = 0 then k
    else helper (k - 1)
  termination_by k
  decreasing_by {
    simp_wf
    cases' k with k'
    · norm_num
    · cases' k' with k''
      · norm_num
      · norm_num
  }
  helper (n - 1)

def implementation (n: Nat) : Nat := max_proper_divisor n

-- LLM HELPER
lemma max_proper_divisor_pos (n: Nat) : 0 < max_proper_divisor n := by
  unfold max_proper_divisor
  split_ifs with h
  · norm_num
  · have : 0 < n := by
      cases' n with n'
      · simp at h
      · norm_num
    let rec helper_pos (k: Nat) (hk_pos: 0 < k) : 0 < max_proper_divisor.helper n k := by
      unfold max_proper_divisor.helper
      split_ifs with h1 h2
      · norm_num
      · norm_num
      · apply helper_pos
        cases' k with k'
        · norm_num at hk_pos
        · cases' k' with k''
          · norm_num at h1
          · norm_num
    apply helper_pos
    cases' n with n'
    · simp at h
    · norm_num

-- LLM HELPER
lemma max_proper_divisor_divides (n: Nat) (hn: 0 < n) : max_proper_divisor n ∣ n := by
  unfold max_proper_divisor
  split_ifs with h
  · cases' n with n'
    · norm_num at hn
    · simp at h
      cases' n' with n''
      · simp
      · simp at h
  · let rec helper_divides (k: Nat) (hk: k ≤ n) : max_proper_divisor.helper n k ∣ n := by
      unfold max_proper_divisor.helper
      split_ifs with h1 h2
      · simp
      · exact Nat.dvd_of_mod_eq_zero h2
      · apply helper_divides
        cases' k with k'
        · norm_num at hk
        · norm_num
        · exact Nat.le_of_succ_le_succ hk
    apply helper_divides
    cases' n with n'
    · norm_num at hn
    · norm_num

-- LLM HELPER
lemma max_proper_divisor_maximal (n: Nat) (hn: 0 < n) (x: Nat) (hx_div: x ∣ n) (hx_ne: x ≠ n) : x ≤ max_proper_divisor n := by
  unfold max_proper_divisor
  split_ifs with h
  · cases' n with n'
    · norm_num at hn
    · simp at h
      cases' n' with n''
      · have : x = 0 ∨ x = 1 := by
          cases' x with x'
          · left; rfl
          · right
            have : x' + 1 ∣ 1 := hx_div
            have : x' + 1 ≤ 1 := Nat.le_of_dvd (by norm_num) this
            cases' x' with x''
            · rfl
            · norm_num at this
        cases' this with h_eq h_eq
        · rw [h_eq]
          norm_num
        · rw [h_eq]
          norm_num
      · simp at h
  · let rec helper_maximal (k: Nat) (hk: k ≤ n) (x: Nat) (hx_div: x ∣ n) (hx_ne: x ≠ n) (hx_le: x ≤ k) : x ≤ max_proper_divisor.helper n k := by
      unfold max_proper_divisor.helper
      split_ifs with h1 h2
      · cases' x with x'
        · norm_num
        · have : x' + 1 ∣ n := hx_div
          have : x' + 1 ≤ n := Nat.le_of_dvd hn this
          have : x' + 1 < n := Nat.lt_of_le_of_ne this hx_ne
          cases' x' with x''
          · norm_num
          · rw [h1] at hx_le
            have : x'' + 1 + 1 ≤ 1 := hx_le
            norm_num at this
      · exact hx_le
      · apply helper_maximal
        · cases' k with k'
          · norm_num at hk
          · norm_num
          · exact Nat.le_of_succ_le_succ hk
        · exact hx_div
        · exact hx_ne
        · cases' k with k'
          · norm_num at hk
          · have : x ≤ k' + 1 := hx_le
            have : x ≤ k' := by
              by_contra h_not_le
              have : x = k' + 1 := by
                have : x ≥ k' + 1 := Nat.le_of_not_gt h_not_le
                exact Nat.le_antisymm hx_le this
              rw [this] at hx_div
              have : n % (k' + 1) = 0 := Nat.mod_eq_zero_of_dvd hx_div
              rw [← this] at h2
              contradiction
            exact this
    have x_lt_n : x < n := by
      by_contra h_not_lt
      have x_le_n : x ≤ n := Nat.le_of_dvd hn hx_div
      have x_ge_n : x ≥ n := Nat.le_of_not_gt h_not_lt
      have x_eq_n : x = n := Nat.le_antisymm x_le_n x_ge_n
      exact hx_ne x_eq_n
    apply helper_maximal
    · cases' n with n'
      · norm_num at hn
      · norm_num
    · exact hx_div
    · exact hx_ne
    · exact Nat.le_sub_of_add_le (Nat.succ_le_of_lt x_lt_n)

theorem correctness
(n: Nat)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  use max_proper_divisor n
  constructor
  · rfl
  · intro hn
    constructor
    · exact max_proper_divisor_pos n
    · constructor
      · exact max_proper_divisor_divides n hn
      · exact max_proper_divisor_maximal n hn