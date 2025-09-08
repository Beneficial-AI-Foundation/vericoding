/- 
function_signature: "def digits(n: int) -> int"
docstring: |
    Given a positive integer n, return the product of the odd digits.
    Return 0 if all digits are even.
test_cases:
  - input: 1
    expected_output: 1
  - input: 4
    expected_output: 0
  - input: 235
    expected_output: 15
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def odd_digit_product_aux (digits : List Nat) : Nat :=
  match digits with
  | [] => 0
  | [d] => if d % 2 = 1 then d else 0
  | d :: ds => 
    let rest_product := odd_digit_product_aux ds
    if d % 2 = 1 then
      if rest_product = 0 then d else rest_product * d
    else rest_product

def implementation (n: Nat) : Nat :=
  if n = 0 then 0
  else
    let digits := Nat.toDigits 10 n
    let odd_digits := digits.filter (fun d => d % 2 = 1)
    if odd_digits.isEmpty then 0
    else odd_digits.prod

def problem_spec
-- function signature
(impl: Nat → Nat)
-- inputs
(n: Nat) :=
-- spec
let spec (result: Nat) :=
  0 < n →
  (n < 10 → (n % 2 = 1 → result = n) ∧ (n % 2 = 0 → result = 0)) ∧
  (10 ≤ n →
    let digit := n % 10;
    let rest := n / 10;
    (digit % 2 = 1 →
      if (Nat.toDigits 10 rest).all (fun x => x % 2 = 0)
        then impl rest = 0 ∧ result = digit
      else
        result = impl rest * digit)
    ∧
    (digit % 2 = 0 →
      result = impl rest))
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER  
lemma implementation_single_digit (d : Nat) (h : d < 10) (hpos : d > 0) : 
  implementation d = if d % 2 = 1 then d else 0 := by
  simp [implementation, hpos]
  rw [Nat.toDigits_digits_lt_base _ (by norm_num) h hpos]
  simp [List.filter, List.isEmpty, List.prod]
  split_ifs with hodd
  · simp [hodd]
  · simp

-- LLM HELPER
lemma digits_all_even_iff (n : Nat) : 
  (Nat.toDigits 10 n).all (fun x => x % 2 = 0) ↔ 
  (Nat.toDigits 10 n).filter (fun x => x % 2 = 1) = [] := by
  simp [List.all_eq_true, List.filter_eq_nil_iff]
  constructor
  · intro h d hd
    exact h d hd
  · intro h d hd
    by_contra hneg
    have : d % 2 = 1 := by omega
    have : d ∈ (Nat.toDigits 10 n).filter (fun x => x % 2 = 1) := by
      simp [List.mem_filter, hd, this]
    rw [h] at this
    exact this

-- LLM HELPER
lemma nat_mod_two_cases (n : Nat) : n % 2 = 0 ∨ n % 2 = 1 := by
  omega

theorem correctness
(n: Nat)
: problem_spec implementation n := by
  use implementation n
  constructor
  · rfl
  · intro hpos
    constructor
    · intro hsingle
      constructor
      · intro hodd
        rw [implementation_single_digit n hsingle hpos]
        simp [hodd]
      · intro heven  
        rw [implementation_single_digit n hsingle hpos]
        simp [heven]
    · intro hbig
      simp [implementation, hpos]
      let digits := Nat.toDigits 10 n
      let odd_digits := digits.filter (fun d => d % 2 = 1)
      constructor
      · intro digit_odd
        split_ifs with hempty
        · simp [hempty]
          constructor
          · simp [implementation]
            have rest_pos : n / 10 > 0 := Nat.div_pos (le_of_lt hbig) (by norm_num)
            simp [rest_pos]
            rw [digits_all_even_iff]
            exfalso
            have digit_in : n % 10 ∈ digits := by
              rw [Nat.mem_toDigits_iff_div_pow_mod_lt]
              · use 0
                simp [Nat.mod_mod]
                constructor
                · exact Nat.mod_lt n (by norm_num)
                · norm_num
              · norm_num
              · exact hpos
            have : n % 10 % 2 = 1 := digit_odd
            have : n % 10 ∈ digits.filter (fun d => d % 2 = 1) := by
              simp [List.mem_filter, digit_in, this]
            rw [hempty] at this
            exact this
          · exact digit_odd
        · constructor
          · simp [implementation]
            have rest_pos : n / 10 > 0 := Nat.div_pos (le_of_lt hbig) (by norm_num)
            simp [rest_pos]
            have : (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1) ≠ [] := by
              by_contra h
              have : digits.filter (fun d => d % 2 = 1) = [n % 10] := by
                have digit_in : n % 10 ∈ digits := by
                  rw [Nat.mem_toDigits_iff_div_pow_mod_lt]
                  · use 0
                    simp [Nat.mod_mod]
                    constructor
                    · exact Nat.mod_lt n (by norm_num)
                    · norm_num
                  · norm_num
                  · exact hpos
                have : n % 10 % 2 = 1 := digit_odd
                simp [digits]
                rw [Nat.toDigits_succ_div_mod (by norm_num) hpos]
                simp [List.filter_cons, this, h]
              rw [this] at hempty
              simp at hempty
            simp [this]
            have : (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1) ≠ [] := this
            simp [this]
            exact (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1)
          · have digit_in : n % 10 ∈ digits := by
              rw [Nat.mem_toDigits_iff_div_pow_mod_lt]
              · use 0
                simp [Nat.mod_mod]
                constructor
                · exact Nat.mod_lt n (by norm_num)
                · norm_num
              · norm_num
              · exact hpos
            have : n % 10 % 2 = 1 := digit_odd
            simp [digits]
            rw [Nat.toDigits_succ_div_mod (by norm_num) hpos]
            simp [List.filter_cons, this, List.prod_cons]
            ring
      · intro digit_even
        simp [implementation]
        have rest_pos : n / 10 > 0 := Nat.div_pos (le_of_lt hbig) (by norm_num)
        simp [rest_pos]
        have : digits.filter (fun d => d % 2 = 1) = (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1) := by
          simp [digits]
          rw [Nat.toDigits_succ_div_mod (by norm_num) hpos]
          simp [List.filter_cons, digit_even]
        rw [this]
        simp [implementation, rest_pos]
        split_ifs
        · rfl
        · rfl