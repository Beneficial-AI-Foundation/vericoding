import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Nat → Nat → Option String)
(n: Nat) (m: Nat) :=
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
∃ result, implementation n m = result ∧
spec result

-- LLM HELPER
def natToBinary (n: Nat) : String :=
  if n = 0 then "0b0"
  else "0b" ++ (Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) n)

def implementation (n: Nat) (m: Nat) : Option String :=
  if n > m then none
  else
    let xs := List.Ico n (m+1)
    let avg := xs.sum / xs.length
    some (natToBinary avg)

-- LLM HELPER
lemma list_ico_length (n m: Nat) (h: n ≤ m) :
  (List.Ico n (m+1)).length = m + 1 - n := by
  rw [List.length_range]
  omega

-- LLM HELPER
lemma nat_to_binary_prefix (n: Nat) :
  (natToBinary n).take 2 = "0b" := by
  unfold natToBinary
  split
  · simp
  · simp

-- LLM HELPER
def binaryStringToNat (s: String) : Nat :=
  Nat.ofDigits 2 (s.toList.map (fun c => c.toNat - '0'.toNat)).reverse

-- LLM HELPER
lemma nat_binary_rec_zero : Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) 0 = "" := by
  rfl

-- LLM HELPER
lemma nat_binary_rec_succ_even (n: Nat) (hn: n > 0) (heven: Even n) :
  Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) n = 
  "0" ++ Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) (n / 2) := by
  have : n = 2 * (n / 2) := by
    rw [← Nat.mul_div_cancel_left (n / 2) (by norm_num)]
    rw [Nat.mul_div_cancel_left n (by norm_num)]
    obtain ⟨k, hk⟩ := heven
    rw [hk]
    rw [Nat.mul_div_cancel_left k (by norm_num)]
  rw [this]
  rw [Nat.binaryRec_eq]
  simp

-- LLM HELPER
lemma nat_binary_rec_succ_odd (n: Nat) (hn: n > 0) (hodd: Odd n) :
  Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) n = 
  "1" ++ Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) (n / 2) := by
  have : n = 2 * (n / 2) + 1 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    rw [Nat.add_mul_div_left 1 k (by norm_num)]
    simp
  rw [this]
  rw [Nat.binaryRec_eq]
  simp

-- LLM HELPER
lemma nat_to_binary_correct (n: Nat) :
  binaryStringToNat (natToBinary n).drop 2 = n := by
  unfold natToBinary binaryStringToNat
  split
  · simp
  · simp
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      cases' n with n'
      · contradiction
      · sorry

theorem correctness
(n: Nat) (m: Nat)
: problem_spec implementation n m := by
  unfold problem_spec implementation
  by_cases h: n > m
  · exists none
    simp [h]
    constructor
    · rfl
    · constructor
      · constructor
        · intro; rfl
        · intro h_contra; exact absurd h_contra (not_le.mpr h)
      · intro h_contra; exact absurd h_contra (not_le.mpr h)
  · push_neg at h
    exists some (natToBinary ((List.Ico n (m + 1)).sum / (List.Ico n (m + 1)).length))
    simp [h]
    constructor
    · rfl
    · constructor
      · constructor
        · intro h_contra; exact absurd h_contra (not_le.mpr (lt_of_not_le h))
        · intro; rfl
      · intro
        simp
        constructor
        · exact nat_to_binary_prefix _
        · rw [← list_ico_length n m h]
          exact nat_to_binary_correct _