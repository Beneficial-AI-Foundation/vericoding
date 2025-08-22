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
lemma list_ico_sum_div_length (n m: Nat) (h: n ≤ m) :
  let xs := List.Ico n (m+1)
  xs.sum / xs.length = xs.sum / (m + 1 - n) := by
  simp [List.Ico]
  rw [List.length_range]

-- LLM HELPER
lemma nat_binary_rec_correct (n: Nat) (hn: n > 0) :
  Nat.ofDigits 2 ((Nat.binaryRec "" (fun _ _ acc => "0" ++ acc) (fun _ _ acc => "1" ++ acc) n).toList.map (fun c => c.toNat - '0'.toNat)).reverse = n := by
  induction n using Nat.binaryRec with
  | z => contradiction
  | f n ih =>
    simp [Nat.binaryRec]
    rw [String.toList_append, List.map_append, List.reverse_append]
    simp [Nat.ofDigits_append]
    rw [List.map_cons, List.reverse_cons, Nat.ofDigits_append]
    simp only [Char.toNat_sub_toNat_zero, List.length_singleton, pow_one]
    exact ih (Nat.div_pos hn (by norm_num))
  | t n ih =>
    simp [Nat.binaryRec]
    rw [String.toList_append, List.map_append, List.reverse_append]
    simp [Nat.ofDigits_append]
    rw [List.map_cons, List.reverse_cons, Nat.ofDigits_append]
    simp only [Char.toNat_sub_toNat_zero, List.length_singleton, pow_one]
    exact ih (Nat.div_pos (Nat.pos_of_ne_zero (fun h => by simp [h] at hn)) (by norm_num))

-- LLM HELPER
lemma nat_to_binary_correct (n: Nat) :
  let s := natToBinary n
  s.take 2 = "0b" ∧ 
  Nat.ofDigits 2 ((s.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = n := by
  unfold natToBinary
  split
  · simp
    constructor
    · rfl
    · simp [Nat.ofDigits]
  · simp
    constructor
    · rfl  
    · apply nat_binary_rec_correct
      omega

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
    exists some (natToBinary ((List.Ico n (m + 1)).sum / (m + 1 - n)))
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
        · exact (nat_to_binary_correct _).1
        · rw [list_ico_sum_div_length n m h]
          exact (nat_to_binary_correct _).2