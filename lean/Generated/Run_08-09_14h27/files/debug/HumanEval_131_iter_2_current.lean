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
lemma implementation_single_digit (d : Nat) (h : d < 10) : 
  implementation d = if d % 2 = 1 then d else 0 := by
  simp [implementation]
  cases' Nat.eq_zero_or_pos d with h0 hpos
  · simp [h0]
  · simp [hpos]
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
        rw [implementation_single_digit n hsingle]
        simp [hodd]
      · intro heven  
        rw [implementation_single_digit n hsingle]
        simp [heven]
    · intro hbig
      simp [implementation]
      simp [hpos]
      let digits := Nat.toDigits 10 n
      let odd_digits := digits.filter (fun d => d % 2 = 1)
      constructor
      · intro digit_odd
        split_ifs with hempty
        · simp [hempty]
          constructor
          · simp [implementation]
            have : n / 10 > 0 := by omega
            simp [this]
            rw [digits_all_even_iff]
            have : digits.filter (fun d => d % 2 = 1) = [] := hempty
            have digit_in : n % 10 ∈ digits := by
              have : digits = Nat.toDigits 10 n := rfl
              rw [this]
              exact Nat.mem_toDigits_mod_base (by norm_num) (by omega)
            have digit_odd_filtered : n % 10 ∉ digits.filter (fun d => d % 2 = 1) := by
              rw [this]
              simp
            simp at digit_odd_filtered
            have : n % 10 % 2 = 0 := digit_odd_filtered digit_in
            omega
          · have : (n % 10) % 2 = 1 := digit_odd
            omega
        · have : odd_digits ≠ [] := hempty
          have : odd_digits.prod > 0 := by
            apply List.one_le_prod_of_one_le
            intro x hx
            have : x ∈ digits.filter (fun d => d % 2 = 1) := hx
            simp at this
            cases' this with h1 h2
            have : x ≥ 1 := by
              have : x < 10 := by
                have : x ∈ Nat.toDigits 10 n := h1
                exact Nat.toDigits_lt_base _ (by norm_num) this
              have : x > 0 := by
                have : x ∈ Nat.toDigits 10 n := h1
                exact Nat.pos_of_mem_toDigits _ this
              omega
            exact this
          have : digits.filter (fun d => d % 2 = 1) = odd_digits := rfl
          constructor
          · simp [implementation]
            have : n / 10 > 0 := by omega
            simp [this]
            have not_all_even : ¬(Nat.toDigits 10 (n / 10)).all (fun x => x % 2 = 0) := by
              by_contra h
              rw [digits_all_even_iff] at h
              have : (Nat.toDigits 10 (n / 10)).filter (fun x => x % 2 = 1) = [] := h
              have digit_in_rest : ∃ d, d ∈ Nat.toDigits 10 (n / 10) ∧ d % 2 = 1 := by
                have : odd_digits ≠ [] := hempty
                have : ∃ d, d ∈ digits.filter (fun x => x % 2 = 1) := by
                  simp [List.ne_nil_iff_exists_mem.mp this]
                cases' this with d hd
                simp at hd
                cases' hd with h1 h2
                use d
                constructor
                · have : d ≠ n % 10 := by
                  sorry -- need to show this digit is not the last one
                  sorry
                · exact h2
              cases' digit_in_rest with d hd
              have : d ∈ (Nat.toDigits 10 (n / 10)).filter (fun x => x % 2 = 1) := by
                simp [hd]
              rw [this] at this
              exact this
            simp [not_all_even]
            exact odd_digits.prod
          · rfl
      · intro digit_even
        simp [implementation]
        have : n / 10 > 0 := by omega
        simp [this]
        have : digits.filter (fun d => d % 2 = 1) = (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1) := by
          have : n % 10 % 2 = 0 := digit_even
          simp [List.filter_cons, this]
          sorry -- need to show digits structure
        rw [this]
        simp [implementation]
        split_ifs
        · rfl
        · rfl