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
lemma implementation_single_digit (d : Nat) (h : d < 10) (hpos : 0 < d) : 
  implementation d = if d % 2 = 1 then d else 0 := by
  simp [implementation]
  simp only [if_neg (ne_of_gt hpos)]
  have : Nat.toDigits 10 d = [d] := by
    exact Nat.toDigits_small 10 h hpos (by norm_num)
  rw [this]
  simp [List.filter, List.isEmpty, List.prod]
  split
  · simp
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
    have : d % 2 = 1 := by
      cases Nat.mod_two_eq_zero_or_one d with
      | inl hzero => exact absurd hzero hneg
      | inr hone => exact hone
    have : d ∈ (Nat.toDigits 10 n).filter (fun x => x % 2 = 1) := by
      simp [List.mem_filter, hd, this]
    rw [h] at this
    exact this

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
      simp [implementation]
      simp only [if_neg (ne_of_gt hpos)]
      constructor
      · intro digit_odd
        split
        · simp only [if_true]
          exfalso
          have digit_in_digits : n % 10 ∈ Nat.toDigits 10 n := by
            apply List.mem_of_mem_append_right
            rw [← Nat.toDigits_succ_div_mod (by norm_num) hpos]
            simp
          have : n % 10 % 2 = 1 := digit_odd
          have : n % 10 ∈ (Nat.toDigits 10 n).filter (fun d => d % 2 = 1) := by
            simp [List.mem_filter, digit_in_digits, this]
          have : (Nat.toDigits 10 n).filter (fun d => d % 2 = 1) ≠ [] := by
            intro h
            rw [h] at this
            exact this
          have : ¬List.isEmpty (Nat.toDigits 10 n).filter (fun d => d % 2 = 1) := by
            rw [List.isEmpty_iff_eq_nil]
            exact this
          assumption
        · simp only [if_false]
          have rest_pos : n / 10 > 0 := Nat.div_pos (le_of_lt hbig) (by norm_num)
          cases h : (Nat.toDigits 10 (n / 10)).all (fun x => x % 2 = 0) with
          | true =>
            constructor
            · simp [implementation]
              simp only [if_neg (ne_of_gt rest_pos)]
              rw [digits_all_even_iff] at h
              rw [h, List.isEmpty_nil, if_true]
              rfl
            · simp [← Nat.toDigits_succ_div_mod (by norm_num) hpos]
              simp [List.filter_cons, digit_odd]
              rw [digits_all_even_iff] at h
              simp [h, List.prod_cons, List.prod_nil]
          | false =>
            simp [← Nat.toDigits_succ_div_mod (by norm_num) hpos]
            simp [List.filter_cons, digit_odd, List.prod_cons]
            simp [implementation]
            simp only [if_neg (ne_of_gt rest_pos)]
            rw [← digits_all_even_iff] at h
            simp [h]
      · intro digit_even
        simp [implementation]
        have rest_pos : n / 10 > 0 := Nat.div_pos (le_of_lt hbig) (by norm_num)
        simp only [if_neg (ne_of_gt rest_pos)]
        have : (Nat.toDigits 10 n).filter (fun d => d % 2 = 1) = 
               (Nat.toDigits 10 (n / 10)).filter (fun d => d % 2 = 1) := by
          rw [← Nat.toDigits_succ_div_mod (by norm_num) hpos]
          simp [List.filter_cons, digit_even]
        rw [this]
        split
        · simp
        · simp