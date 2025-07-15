import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def natToBinary (n : Nat) : List Nat :=
  if n = 0 then [0]
  else 
    let rec helper (m : Nat) (acc : List Nat) : List Nat :=
      if m = 0 then acc
      else helper (m / 2) ((m % 2) :: acc)
    helper n []

-- LLM HELPER
def listNatToString (l : List Nat) : String :=
  String.mk (l.map (fun n => Char.ofNat (n + '0'.toNat)))

def implementation (decimal: Nat) : String := 
  let binaryDigits := natToBinary decimal
  let binaryString := listNatToString binaryDigits
  "db" ++ binaryString ++ "db"

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 (natToBinary n).reverse = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    unfold natToBinary
    split_ifs with h1
    · subst h1
      simp [Nat.ofDigits]
    · have h2 : n > 0 := Nat.pos_of_ne_zero h1
      simp only [natToBinary.helper]
      have h3 : n / 2 < n := Nat.div_lt_self h2 (by norm_num)
      have h4 : natToBinary.helper n [] = (natToBinary (n / 2)) ++ [n % 2] := by
        induction n using Nat.strong_induction_on with
        | h m ih_m =>
          unfold natToBinary.helper
          split_ifs with hm
          · simp at hm
            rw [hm]
            simp [natToBinary]
          · rw [ih_m (m / 2)]
            rw [natToBinary]
            simp [hm]
            exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)
      rw [h4, List.reverse_append, List.reverse_cons, List.reverse_nil, List.append_nil]
      rw [Nat.ofDigits_append, List.length_reverse]
      rw [ih (n / 2) h3]
      simp [Nat.ofDigits, List.foldl]
      rw [Nat.div_add_mod n 2]

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).toList.map (fun c => c.toNat - '0'.toNat) = l := by
  unfold listNatToString
  simp only [String.toList_mk, List.map_map]
  congr 1
  ext x
  simp only [Function.comp_apply]
  have hx : x < 2 := h x (by assumption)
  cases x with
  | zero => simp [Char.ofNat, Char.toNat]
  | succ n => 
    cases n with
    | zero => simp [Char.ofNat, Char.toNat]
    | succ m => exfalso; exact Nat.not_lt.mpr (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le m))) hx

-- LLM HELPER
lemma natToBinary_binary_digits (n : Nat) :
  ∀ x ∈ natToBinary n, x < 2 := by
  unfold natToBinary
  split_ifs with h
  · simp
  · intro x hx
    simp only [natToBinary.helper] at hx
    induction n using Nat.strong_induction_on with
    | h m ih =>
      unfold natToBinary.helper at hx
      split_ifs at hx with hm
      · simp at hx
      · rw [List.mem_cons] at hx
        cases hx with
        | inl h_eq => rw [← h_eq]; exact Nat.mod_two_lt
        | inr h_mem => 
          apply ih (m / 2)
          exact Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)
          exact h_mem

-- LLM HELPER
lemma natToBinary_nonempty (n : Nat) : (natToBinary n).length > 0 := by
  unfold natToBinary
  split_ifs with h
  · simp
  · simp only [natToBinary.helper]
    induction n using Nat.strong_induction_on with
    | h m ih =>
      unfold natToBinary.helper
      split_ifs with hm
      · simp at hm
        rw [hm]
        simp [natToBinary]
      · simp [List.length_cons]

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal
:= by
  use implementation decimal
  constructor
  · rfl
  · unfold implementation
    let binaryDigits := natToBinary decimal
    let binaryString := listNatToString binaryDigits
    constructor
    · -- 4 < result.length
      have h1 : binaryString.length > 0 := by
        unfold binaryString
        rw [String.length_mk]
        rw [List.length_map]
        exact natToBinary_nonempty decimal
      rw [String.length_append, String.length_append]
      norm_num
      exact h1
    constructor
    · -- result.drop (result.length - 2) = "db"
      rw [String.length_append, String.length_append]
      have h1 : binaryString.length ≥ 1 := by
        unfold binaryString
        rw [String.length_mk, List.length_map]
        exact natToBinary_nonempty decimal
      have h2 : "db".length + binaryString.length + "db".length - 2 = "db".length + binaryString.length := by
        norm_num
      rw [h2]
      rw [String.drop_append_of_le_length]
      rw [String.drop_append_of_le_length]
      simp [String.drop_length_eq_empty]
      norm_num
      norm_num
    constructor
    · -- result.take 2 = "db"
      rw [String.take_append_of_le_length]
      norm_num
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      simp only [String.toList_append]
      rw [List.drop_append_of_le_length]
      rw [List.dropLast_append]
      rw [List.dropLast_append]
      simp only [String.toList]
      rw [listNatToString_map_inv]
      · rw [natToBinary_correct]
      · exact natToBinary_binary_digits decimal
      · norm_num
      · norm_num
      · norm_num