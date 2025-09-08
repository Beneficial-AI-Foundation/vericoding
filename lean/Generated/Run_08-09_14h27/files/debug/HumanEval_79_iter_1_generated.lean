/- 
function_signature: "def decimal_to_binary(decimal: nat) -> string"
docstring: |
    You will be given a number in decimal form and your task is to convert it to
    binary format. The function should return a string, with each character representing a binary
    number. Each character in the string will be '0' or '1'.

    There will be an extra couple of characters 'db' at the beginning and at the end of the string.
    The extra characters are there to help with the format.
test_cases:
  - input: 15
    expected_output: "db1111db"
  - input: 32
    expected_output: "db100000db"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def nat_to_binary_digits (n : Nat) : List Nat :=
  if n = 0 then [0] else
    let rec aux (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else aux (m / 2) ((m % 2) :: acc)
    aux n []

-- LLM HELPER
def digits_to_string (digits : List Nat) : String :=
  String.mk (digits.map (fun d => Char.ofNat (d + '0'.toNat)))

def implementation (decimal: Nat) : String :=
  let binary_digits := nat_to_binary_digits decimal
  let binary_string := digits_to_string binary_digits
  "db" ++ binary_string ++ "db"

def problem_spec
-- function signature
(implementation: Nat → String)
-- inputs
(decimal: Nat) :=
-- spec
let spec (result: String) :=
  4 < result.length ∧
  result.drop (result.length - 2) = "db" ∧
  result.take 2 = "db" ∧
  let resultTrimmed := (result.toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat)
  decimal = Nat.ofDigits 2 resultTrimmed.reverse
-- program termination
∃ result, implementation decimal = result ∧
spec result

-- LLM HELPER
lemma nat_to_binary_digits_correct (n : Nat) : 
  n = Nat.ofDigits 2 (nat_to_binary_digits n).reverse := by
  sorry

-- LLM HELPER  
lemma digits_to_string_correct (digits : List Nat) :
  (digits.all (fun d => d < 2)) →
  digits = (digits_to_string digits).toList.map (fun c => c.toNat - '0'.toNat) := by
  sorry

-- LLM HELPER
lemma nat_to_binary_digits_all_lt_two (n : Nat) :
  (nat_to_binary_digits n).all (fun d => d < 2) := by
  sorry

-- LLM HELPER
lemma nat_to_binary_digits_nonempty (n : Nat) :
  (nat_to_binary_digits n).length > 0 := by
  sorry

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal
:= by
  simp [problem_spec, implementation]
  use "db" ++ digits_to_string (nat_to_binary_digits decimal) ++ "db"
  constructor
  · rfl
  · simp [digits_to_string]
    constructor
    · -- Length > 4
      have h1 : (nat_to_binary_digits decimal).length > 0 := nat_to_binary_digits_nonempty decimal
      simp [String.length_mk, String.length_append]
      omega
    constructor
    · -- Ends with "db"
      simp [String.drop_append, String.length_mk, String.length_append]
    constructor  
    · -- Starts with "db"
      simp [String.take_append]
    · -- Correctness of binary conversion
      simp [String.toList_append, String.toList_mk, List.drop_append, List.dropLast_append]
      have h1 := nat_to_binary_digits_correct decimal
      have h2 := digits_to_string_correct (nat_to_binary_digits decimal)
      have h3 := nat_to_binary_digits_all_lt_two decimal
      rw [← h1]
      congr 1
      exact (h2 h3).symm