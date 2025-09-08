/- 
function_signature: "def rounded_avg(n: nat, m: nat) -> Option[string]"
docstring: |
    You are given two positive integers n and m, and your task is to compute the
    average of the integers from n through m (including n and m).
    Round the answer to the nearest integer and convert that to binary.
    If n is greater than m, return none.
test_cases:
  - input: (1, 5)
    expected_output: "0b11"
  - input: (7, 5)
    expected_output: None
  - input: (10, 20)
    expected_output: "0b1111"
  - input: (20, 33)
    expected_output: "0b11010"
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def nat_to_binary (n : Nat) : String :=
  if n = 0 then "0" else
  let rec helper (n : Nat) : String :=
    if n = 0 then ""
    else helper (n / 2) ++ (if n % 2 = 1 then "1" else "0")
  helper n

-- LLM HELPER
def round_rat_to_nat (r : Rat) : Nat :=
  let floor_val := Int.natAbs (Int.floor r)
  let frac := r - Int.floor r
  if frac < 1/2 then floor_val
  else floor_val + 1

def implementation (n: Nat) (m: Nat) : Option String :=
  if n > m then none
  else
    let count := m - n + 1
    let sum := count * (n + m) / 2
    let avg_rat : Rat := sum / count
    let rounded := round_rat_to_nat avg_rat
    some ("0b" ++ nat_to_binary rounded)

def problem_spec
-- function signature
(implementation: Nat → Nat → Option String)
-- inputs
(n: Nat) (m: Nat) :=
-- spec
let spec (result: Option String) :=
  (n > m ↔ result.isNone) ∧
  (n ≤ m ↔ result.isSome) ∧
  (n ≤ m →
    (result.isSome ∧
    let val := Option.getD result "";
    let xs := List.Ico n (m+1);
    let avg := xs.sum / xs.length;
    (val.take 2 = "0b") ∧
    (Nat.ofDigits 2 ((val.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = avg)))
-- program termination
∃ result, implementation n m = result ∧
spec result

-- LLM HELPER
lemma list_ico_sum (n m : Nat) (h : n ≤ m) : 
  (List.Ico n (m + 1)).sum = (m - n + 1) * (n + m) / 2 := by
  have h1 : List.Ico n (m + 1) = List.range (m + 1 - n) |>.map (· + n) := by simp [List.Ico]
  simp [List.sum_range, Nat.add_sub_cancel']
  ring_nf

-- LLM HELPER
lemma list_ico_length (n m : Nat) (h : n ≤ m) :
  (List.Ico n (m + 1)).length = m - n + 1 := by
  simp [List.length_Ico]
  omega

-- LLM HELPER
lemma round_rat_eq_div (sum count : Nat) (h : count > 0) :
  round_rat_to_nat ((sum : Rat) / count) = sum / count := by
  simp [round_rat_to_nat]
  have h1 : ((sum : Rat) / count).floor = (sum / count : ℤ) := by
    simp [Rat.floor_div_nat]
  simp [h1]
  have h2 : ((sum : Rat) / count) - (sum / count : ℤ) = 0 := by
    simp [Rat.sub_floor]
    ring
  simp [h2]
  simp [Int.natAbs_of_nonneg]

-- LLM HELPER
lemma nat_to_binary_correct (n : Nat) :
  Nat.ofDigits 2 (nat_to_binary n).toList.map (fun c => c.toNat - '0'.toNat) |>.reverse = n := by
  induction n using Nat.strong_induction_on with
  | h n ih => 
    simp [nat_to_binary]
    split_ifs with h
    · simp [h]
    · simp [Nat.ofDigits_digits]

theorem correctness
(n: Nat) (m: Nat)
: problem_spec implementation n m := by
  unfold problem_spec
  unfold implementation
  split_ifs with h
  · -- Case: n > m
    use none
    constructor
    · simp
    · constructor
      · simp [h]
      · constructor
        · simp [le_iff_lt_or_eq, h]
          omega
        · intro h_le
          exfalso
          omega
  · -- Case: n ≤ m
    push_neg at h
    let count := m - n + 1
    let sum := count * (n + m) / 2
    let avg_rat : Rat := sum / count
    let rounded := round_rat_to_nat avg_rat
    use some ("0b" ++ nat_to_binary rounded)
    constructor
    · simp
    · constructor
      · simp [h]
      · constructor
        · simp [h]
        · intro h_le
          constructor
          · simp
          · constructor
            · simp [Option.getD]
              ring
            · have h_eq : (List.Ico n (m + 1)).sum = sum := by
                rw [list_ico_sum n m h]
              have h_len : (List.Ico n (m + 1)).length = count := by
                rw [list_ico_length n m h]
              have h_pos : count > 0 := by
                simp [count]
                omega
              simp [Option.getD]
              rw [h_eq, h_len]
              rw [round_rat_eq_div sum count h_pos]
              simp [nat_to_binary_correct]

-- #test implementation 1 5 = some "0b11"
-- #test implementation 7 13 = some "0b1010"
-- #test implementation 964 977 = some "0b1111001010"
-- #test implementation 996 997 = some "0b1111100100"
-- #test implementation 185 546 = some "0b101101110"
-- #test implementation 362 496 = some "0b110101101"
-- #test implementation 350 902 = some "0b1001110010"
-- #test implementation 197 233 = some "0b11010111"
-- #test implementation 7 5 = none
-- #test implementation 5 1 = none
-- #test implementation 5 5 = some "0b101"