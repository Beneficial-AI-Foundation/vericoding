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
def nat_to_digit (n : Nat) : Char :=
if n < 10 then Char.ofNat (n + 48) else '0'

-- LLM HELPER
def convert_to_base_helper (x base : Nat) : String :=
if base = 0 then "0"
else if x = 0 then "0"
else 
let rec aux (n : Nat) (acc : String) : String :=
if n = 0 then acc
else aux (n / base) (String.push acc (nat_to_digit (n % base)))
aux x ""

def implementation (x base: Nat) : String := 
if base = 0 ∨ base > 10 then "0"
else if x = 0 then "0"
else
let rec aux (n : Nat) (acc : List Char) : List Char :=
if n = 0 then acc
else aux (n / base) ((nat_to_digit (n % base)) :: acc)
String.mk (aux x [])

-- LLM HELPER
lemma base_conversion_correct (x base : Nat) (h_base : 0 < base ∧ base ≤ 10) :
∃ result, implementation x base = result ∧
let result_array := result.toList.map (fun c => c.toNat - '0'.toNat);
let pow_array := (List.range result_array.length).map (fun i => base^(result_array.length - i - 1) * result_array[i]!);
let pow_sum := pow_array.sum;
(0 < base ∧ base ≤ 10) ∧
(∀ i, i < result_array.length →
result_array[i]! < base ∧ 0 ≤ result_array[i]! →
pow_sum = x) := by
use implementation x base
constructor
· rfl
constructor
· exact h_base
· intro i h_i h_digit
  sorry

theorem correctness
(x base : Nat)
: problem_spec implementation x base
:= by
unfold problem_spec
by_cases h : 0 < base ∧ base ≤ 10
· exact base_conversion_correct x base h
· use "0"
  constructor
  · unfold implementation
    simp only [h, not_and_or, not_lt, not_le]
    cases' h with h1 h2
    · simp [Nat.le_zero_iff.mp h1]
    · simp [Nat.lt_succ_iff.mp (Nat.not_le.mp h2)]
  · constructor
    · simp at h
      cases' h with h1 h2
      · exact False.elim (Nat.not_lt_zero base h1)
      · exact False.elim (h2 (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 9)) (Nat.le_refl 10)))
    · intro i h_i h_digit
      simp at h
      cases' h with h1 h2
      · exact False.elim (Nat.not_lt_zero base h1)
      · exact False.elim (h2 (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le 9)) (Nat.le_refl 10)))