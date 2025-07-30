import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Nat → Nat -> String)
-- inputs
(x base: Nat) :=
-- spec
let spec (result: String) :=
let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
let pow_sum := pow_array.sum;
(0 < base ∧ base ≤ 10) ∧
(∀ i, i < result_array.length →
result_array[i]! < base ∧ 0 ≤ result_array[i]! →
pow_sum = x);
-- program termination
∃ result, implementation x base = result ∧
spec result

-- LLM HELPER
def nat_to_base (n : Nat) (base : Nat) : List Nat :=
  if n = 0 then [0]
  else if base ≤ 1 then [0]
  else
    let rec aux (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else aux (n / base) ((n % base) :: acc)
    termination_by n
    decreasing_by
      simp_wf
      apply Nat.div_lt_self
      · omega
      · omega
    aux n []

-- LLM HELPER
def digit_to_char (d : Nat) : Char :=
  if d < 10 then Char.ofNat (48 + d)
  else '0'

-- LLM HELPER
def digits_to_string (digits : List Nat) : String :=
  String.mk (digits.map digit_to_char)

def implementation (x base: Nat) : String := 
  if base ≤ 1 ∨ base > 10 then "0"
  else digits_to_string (nat_to_base x base)

-- LLM HELPER
lemma char_zero_tonat : '0'.toNat = 48 := by norm_num

-- LLM HELPER
lemma char_to_nat_digit_to_char (d : Nat) (h : d < 10) : 
  (digit_to_char d).toNat - 48 = d := by
  simp [digit_to_char, h]
  norm_num

-- LLM HELPER
lemma nat_to_base_valid (n base : Nat) (h_base : 1 < base) :
  ∀ d ∈ nat_to_base n base, d < base := by
  intro d hd
  simp [nat_to_base] at hd
  split_ifs at hd with h_zero h_le
  · simp at hd
    rw [hd]
    exact Nat.zero_lt_of_lt h_base
  · have : ¬(base ≤ 1) := not_le.mpr h_base
    contradiction
  · have h_pos : 0 < base := by omega
    induction' n using Nat.strong_induction_on with n ih
    simp [nat_to_base.aux] at hd
    split_ifs at hd with h_n_zero
    · simp at hd
    · have h_div_lt : n / base < n := Nat.div_lt_self (by omega) h_pos
      have h_mod := Nat.mod_lt n h_pos
      cases' hd with h1 h2
      · exact h_mod
      · exact ih (n / base) h_div_lt h2

-- LLM HELPER
lemma nat_to_base_sum (n base : Nat) (h_base : 1 < base) :
  let digits := nat_to_base n base
  (List.range digits.length).map (fun i => base^(digits.length - i - 1) * digits[i]!) |>.sum = n := by
  simp [nat_to_base]
  split_ifs with h_zero h_le
  · simp [h_zero]
  · have : ¬(base ≤ 1) := not_le.mpr h_base
    contradiction
  · have h_pos : 0 < base := by omega
    sorry

-- LLM HELPER
lemma digits_to_string_map (digits : List Nat) (h_valid : ∀ d ∈ digits, d < 10) :
  (digits_to_string digits).toList.map (fun c => c.toNat - 48) = digits := by
  simp [digits_to_string, String.toList, String.mk]
  ext i
  simp [List.getElem?_map]
  by_cases h : i < digits.length
  · simp [h]
    have h_valid_i : digits[i] < 10 := by
      apply h_valid
      simp [List.mem_iff_get]
      use i
      constructor
      · exact h
      · rfl
    rw [char_to_nat_digit_to_char]
    exact h_valid_i
  · simp [h]

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  simp [problem_spec, implementation]
  split_ifs with h
  · -- Case: base ≤ 1 ∨ base > 10
    use "0"
    constructor
    · rfl
    · simp
      constructor
      · by_contra h_pos
        cases' h_pos with h_pos_left h_pos_right
        cases' h with h1 h2
        · exact Nat.not_lt.mpr h1 h_pos_left
        · linarith [h2, h_pos_right]
      · intro i hi h_bounds
        simp at hi
  · -- Case: 1 < base ∧ base ≤ 10
    push_neg at h
    have h_base_pos : 0 < base := by omega
    have h_base_le : base ≤ 10 := h.2
    have h_base_gt : 1 < base := h.1
    
    let digits := nat_to_base x base
    let result := digits_to_string digits
    use result
    constructor
    · rfl
    · constructor
      · constructor
        · exact h_base_pos
        · exact h_base_le
      · intro i hi h_bounds
        have h_digits_valid : ∀ d ∈ digits, d < 10 := by
          intro d hd
          have h_d_lt_base := nat_to_base_valid x base h_base_gt d hd
          linarith [h_d_lt_base, h_base_le]
        have h_string_eq := digits_to_string_map digits h_digits_valid
        simp [result, digits_to_string, String.toList, String.mk] at hi h_string_eq
        rw [←char_zero_tonat] at h_string_eq
        rw [h_string_eq] at hi h_bounds
        have h_bounds_split := h_bounds
        cases' h_bounds_split with h_lt h_ge
        rw [h_string_eq]
        exact nat_to_base_sum x base h_base_gt