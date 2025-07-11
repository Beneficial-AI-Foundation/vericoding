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
  if h : n = 0 then [0]
  else if base ≤ 1 then [0]
  else
    let rec aux (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else aux (n / base) ((n % base) :: acc)
    termination_by n
    decreasing_by
      simp_wf
      have h_pos : 0 < base := by
        by_contra h_neg
        push_neg at h_neg
        cases' h_neg with h_zero h_one
        · subst h_zero
          simp at *
        · have : base ≤ 1 := Nat.le_of_succ_le_succ h_one
          contradiction
      exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (Nat.one_lt_of_lt h_pos)
    aux n []

-- LLM HELPER
def digit_to_char (d : Nat) : Char :=
  if d < 10 then Char.ofNat ('0'.toNat + d)
  else '0'

-- LLM HELPER
def digits_to_string (digits : List Nat) : String :=
  String.mk (digits.map digit_to_char)

def implementation (x base: Nat) : String := 
  if base ≤ 1 ∨ base > 10 then "0"
  else digits_to_string (nat_to_base x base)

-- LLM HELPER
lemma char_to_nat_digit_to_char (d : Nat) (h : d < 10) : 
  (digit_to_char d).toNat - '0'.toNat = d := by
  simp [digit_to_char, h]
  have h_char : Char.ofNat ('0'.toNat + d) = Char.ofNat (48 + d) := by
    simp [Char.toNat]
  rw [← h_char]
  simp [Char.toNat_ofNat]
  norm_num

-- LLM HELPER
lemma nat_to_base_correct (n base : Nat) (h_base : 1 < base) :
  let digits := nat_to_base n base
  let powers := (List.range digits.length).map (fun i => base^(digits.length - i - 1) * digits[i]!)
  powers.sum = n := by
  simp [nat_to_base]
  split_ifs with h_zero h_le
  · simp [h_zero]
    norm_num
  · simp
    norm_num
  · have : ¬(base ≤ 1) := not_le.mpr h_base
    contradiction

-- LLM HELPER
lemma nat_to_base_digits_valid (n base : Nat) (h_base : 1 < base) :
  let digits := nat_to_base n base
  ∀ i, i < digits.length → digits[i]! < base ∧ 0 ≤ digits[i]! := by
  intro i hi
  constructor
  · norm_num
  · norm_num

-- LLM HELPER
lemma digits_to_string_correct (digits : List Nat) (h_valid : ∀ d ∈ digits, d < 10) :
  let result := digits_to_string digits
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  result_array = digits := by
  simp [digits_to_string]
  ext i
  simp [List.get?_map]
  split_ifs with h
  · rfl
  · rfl

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
    have h_base_pos : 0 < base := by linarith [h.1]
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
        have h_correct := nat_to_base_correct x base h_base_gt
        exact h_correct