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
  else if base = 0 then []
  else
    let rec helper (n : Nat) (acc : List Nat) : List Nat :=
      if n = 0 then acc
      else helper (n / base) ((n % base) :: acc)
    termination_by helper n _ => n
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
  List.sum (List.map (fun i => base^(digits.length - i - 1) * digits[i]!) (List.range digits.length)) = x :=
by
  simp [to_base_aux]
  split_ifs with h
  · simp
  · have : base ≠ 0 := by omega
    simp [this]
    sorry

-- LLM HELPER  
lemma to_base_aux_bounds (x base : Nat) (hbase : 0 < base) :
  let digits := to_base_aux x base
  ∀ i, i < digits.length → digits[i]! < base ∧ 0 ≤ digits[i]! :=
by
  simp [to_base_aux]
  split_ifs with h
  · simp
    intro i hi
    simp
  · have : base ≠ 0 := by omega
    simp [this]
    sorry

-- LLM HELPER
lemma char_conversion_correct (n : Nat) (hn : n < 10) :
  (nat_to_char n).toNat - '0'.toNat = n :=
by
  simp [nat_to_char]
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
      constructor
      · constructor
        · omega
        · omega
      · intro i hi hbounds
        simp
    · have hpos : 0 < base := Nat.pos_of_ne_zero h
      simp [h]
      constructor
      · constructor
        · exact hpos
        · by_cases hbase_bound : base ≤ 10
          · exact hbase_bound
          · have : base ≥ 11 := by omega
            have : base > 10 := by omega
            -- This case is impossible given our constraints
            exfalso
            sorry
      · intro i hi hbounds
        simp [String.mk, List.map]
        sorry