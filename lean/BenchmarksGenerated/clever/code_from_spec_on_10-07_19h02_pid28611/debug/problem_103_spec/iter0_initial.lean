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
  else "0b" ++ (Nat.binaryRec "" (fun _ _ acc => acc ++ "0") (fun _ _ acc => acc ++ "1") n)

def implementation (n: Nat) (m: Nat) : Option String :=
  if n > m then none
  else
    let xs := List.Ico n (m+1)
    let avg := xs.sum / xs.length
    some (natToBinary avg)

-- LLM HELPER
lemma list_ico_sum_div_length (n m: Nat) (h: n ≤ m) :
  let xs := List.Ico n (m+1)
  xs.sum / xs.length = (n + m) / 2 := by
  sorry

-- LLM HELPER
lemma nat_binary_rec_correct (n: Nat) (hn: n > 0) :
  Nat.ofDigits 2 ((Nat.binaryRec "" (fun _ _ acc => acc ++ "0") (fun _ _ acc => acc ++ "1") n).toList.map (fun c => c.toNat - '0'.toNat)).reverse = n := by
  sorry

-- LLM HELPER
lemma nat_to_binary_correct (n: Nat) :
  let s := natToBinary n
  s.take 2 = "0b" ∧ 
  Nat.ofDigits 2 ((s.drop 2).toList.map (fun c => c.toNat - '0'.toNat)).reverse = n := by
  unfold natToBinary
  split
  · simp
  · simp
    apply nat_binary_rec_correct
    assumption

theorem correctness
(n: Nat) (m: Nat)
: problem_spec implementation n m := by
  unfold problem_spec implementation
  by_cases h: n > m
  · simp [h]
    constructor
    · constructor
      · intro; rfl
      · intro h_contra; exact absurd h_contra (not_le.mpr h)
    · intro h_contra; exact absurd h_contra (not_le.mpr h)
  · push_neg at h
    simp [h]
    constructor
    · constructor
      · intro h_contra; exact absurd h_contra (not_le.mpr (lt_of_not_le h))
      · intro; rfl
    · intro
      simp
      constructor
      · exact (nat_to_binary_correct _).1
      · rw [list_ico_sum_div_length n m h]
        exact (nat_to_binary_correct _).2