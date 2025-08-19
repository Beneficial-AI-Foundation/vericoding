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
def nat_to_digit (n: Nat) : Char :=
  Char.ofNat (n + '0'.toNat)

-- LLM HELPER
def convert_to_base_helper (x base: Nat) : String :=
  if x = 0 then "0"
  else if base ≤ 1 then "0"
  else
    let rec aux (n: Nat) (acc: String) : String :=
      if n = 0 then acc
      else aux (n / base) ((nat_to_digit (n % base)).toString ++ acc)
    aux x ""

def implementation (x base: Nat) : String := 
  convert_to_base_helper x base

-- LLM HELPER
lemma char_to_nat_nat_to_digit (n: Nat) (h: n < 10) : 
  (nat_to_digit n).toNat - '0'.toNat = n := by
  unfold nat_to_digit
  simp [Char.toNat_ofNat]
  sorry

-- LLM HELPER
lemma convert_correct (x base: Nat) (h1: 0 < base) (h2: base ≤ 10) :
  let result := convert_to_base_helper x base
  let result_array := result.toList.map (fun c => c.toNat - '0'.toNat)
  let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!)
  let pow_sum := pow_array.sum
  (∀ i, i < result_array.length → result_array[i]! < base ∧ 0 ≤ result_array[i]!) ∧ 
  pow_sum = x := by
  sorry

theorem correctness
(x base : Nat)
: problem_spec implementation x base := by
  unfold problem_spec implementation
  simp only [convert_to_base_helper]
  by_cases h1: 0 < base
  · by_cases h2: base ≤ 10
    · use convert_to_base_helper x base
      constructor
      · rfl
      · constructor
        · exact ⟨h1, h2⟩
        · intro i hi
          intro h_bounds
          have conv_correct := convert_correct x base h1 h2
          exact conv_correct.2
    · use "0"
      constructor
      · simp [convert_to_base_helper]
        split_ifs with h3
        · rfl
        · simp at h2
          have : base ≤ 1 := Nat.lt_succ_iff.mp (Nat.not_le.mp h2)
          rfl
      · exfalso
        exact h2 (Nat.zero_lt_one.trans h1)
  · use "0"
    constructor
    · simp [convert_to_base_helper]
      split_ifs with h3
      · rfl
      · simp at h1
        rfl
    · exfalso
      exact h1 (Nat.zero_lt_one.trans_le (Nat.succ_le_iff.mpr (Nat.zero_lt_one)))