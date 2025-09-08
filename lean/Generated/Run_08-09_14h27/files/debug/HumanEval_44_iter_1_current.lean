/- 
function_signature: "def change_base(x: Nat, base: Nat) -> String"
docstring: |
    Change numerical base of input number x to base.
    return string representation after the conversion.
    base numbers are less than 10.
test_cases:
  - input: (8, 3)
    expected_output: '22'
  - input: (8, 2)
    expected_output: '1000'
  - input: (7, 2)
    expected_output: '111'
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def to_base_aux (x base : Nat) : List Nat :=
  if x = 0 then [0]
  else
    let rec helper (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else helper (n / base) ((n % base) :: acc)
    helper x []

-- LLM HELPER
def nat_to_char (n : Nat) : Char :=
  Char.ofNat (n + '0'.toNat)

def implementation (x base: Nat) : String :=
  if base = 0 then ""
  else
    let digits := to_base_aux x base
    String.mk (digits.map nat_to_char)

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
lemma to_base_aux_correct (x base : Nat) (hbase : 0 < base) :
  let digits := to_base_aux x base
  (List.range digits.length).sum (fun i => base^(digits.length - i - 1) * digits[i]!) = x :=
by
  sorry

-- LLM HELPER  
lemma to_base_aux_bounds (x base : Nat) (hbase : 0 < base) :
  let digits := to_base_aux x base
  ∀ i, i < digits.length → digits[i]! < base ∧ 0 ≤ digits[i]! :=
by
  sorry

-- LLM HELPER
lemma char_conversion_correct (n : Nat) (hn : n < 10) :
  (nat_to_char n).toNat - '0'.toNat = n :=
by
  sorry

theorem correctness
(x base : Nat)
: problem_spec implementation x base
:= by
  unfold problem_spec
  use implementation x base
  constructor
  · rfl
  · unfold implementation
    by_cases h : base = 0
    · simp [h]
      sorry
    · have hpos : 0 < base := Nat.pos_of_ne_zero h
      simp [to_base_aux]
      constructor
      · constructor
        · exact hpos
        · sorry -- need base ≤ 10 assumption
      · intro i hi
        intro hbounds
        sorry -- use helper lemmas

-- #test implementation 8 3 = '22'
-- #test implementation 8 2 = '1000'
-- #test implementation 7 2 = '111'