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
  String.mk (l.map (fun n => Char.ofNat (n + 48)))

def implementation (decimal: Nat) : String := 
  let binaryDigits := natToBinary decimal
  let binaryString := listNatToString binaryDigits
  "db" ++ binaryString ++ "db"

-- LLM HELPER
lemma natToBinary_correct (n : Nat) : 
  Nat.ofDigits 2 (natToBinary n).reverse = n := by
  if h : n = 0 then
    rw [h, natToBinary]
    simp [Nat.ofDigits]
  else
    induction n using Nat.strong_induction_on with
    | h n ih =>
      if h_zero : n = 0 then
        rw [h_zero, natToBinary]
        simp [Nat.ofDigits]
      else
        unfold natToBinary
        rw [if_neg h_zero]
        have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h_zero) (by norm_num)
        have h_div_zero : n / 2 = 0 ∨ n / 2 ≠ 0 := by simp
        cases h_div_zero with
        | inl h_div_z =>
          rw [natToBinary.helper]
          rw [if_neg h_zero]
          rw [h_div_z]
          rw [natToBinary.helper]
          simp
          rw [Nat.ofDigits]
          simp
          rw [Nat.mod_two_eq_zero_or_one] at *
          cases (Nat.mod_two_eq_zero_or_one n) with
          | inl h_mod => 
            rw [h_mod]
            have : n = 2 * (n / 2) := by rw [← Nat.div_add_mod n 2, h_mod]; simp
            rw [this, h_div_z]; simp
          | inr h_mod => 
            rw [h_mod]
            have : n = 2 * (n / 2) + 1 := by rw [← Nat.div_add_mod n 2, h_mod]
            rw [this, h_div_z]; simp
        | inr h_div_nz =>
          have ih_div := ih (n / 2) div_lt h_div_nz
          rw [natToBinary.helper]
          rw [if_neg h_zero]
          rw [natToBinary.helper]
          rw [if_neg h_div_nz]
          have : natToBinary.helper (n / 2) ((n % 2) :: []) = (n % 2) :: natToBinary.helper (n / 2) [] := by
            simp [natToBinary.helper]
          rw [this]
          have : natToBinary.helper (n / 2) [] = natToBinary (n / 2) := by
            rw [natToBinary, if_neg h_div_nz]
          rw [this]
          rw [List.reverse_cons]
          rw [Nat.ofDigits_append]
          rw [List.reverse_singleton]
          rw [Nat.ofDigits_singleton]
          rw [ih_div]
          rw [← Nat.div_add_mod n 2]
          ring

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).data.map (fun c => c.toNat - 48) = l := by
  unfold listNatToString
  rw [String.mk]
  rw [List.map_map]
  congr 1
  ext x
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
  if h : n = 0 then
    rw [if_pos h]
    intro x hx
    simp at hx
    rw [hx]
    norm_num
  else
    rw [if_neg h]
    intro x hx
    have : ∀ m acc, ∀ x ∈ natToBinary.helper m acc, x < 2 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro acc x hx
        simp [natToBinary.helper] at hx
        if hm : m = 0 then
          rw [if_pos hm] at hx
          exact hx
        else
          rw [if_neg hm] at hx
          cases hx with
          | inl h => rw [h]; norm_num
          | inr h => exact ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)) ((m % 2) :: acc) x h
    exact this n [] x hx

-- LLM HELPER
lemma natToBinary_nonempty (n : Nat) : (natToBinary n).length > 0 := by
  unfold natToBinary
  if h : n = 0 then
    rw [if_pos h]
    simp
  else
    rw [if_neg h]
    have : ∀ m acc, m > 0 → (natToBinary.helper m acc).length > 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro acc hm_pos
        rw [natToBinary.helper]
        if hm : m = 0 then
          rw [if_pos hm] at hm_pos
          exact absurd hm_pos (Nat.not_lt.mpr (Nat.zero_le 0))
        else
          rw [if_neg hm]
          exact ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)) ((m % 2) :: acc) (Nat.pos_of_ne_zero hm)
    exact this n [] (Nat.pos_of_ne_zero h)

-- LLM HELPER
lemma listNatToString_length (l : List Nat) : (listNatToString l).length = l.length := by
  unfold listNatToString
  rw [String.length_mk]

theorem correctness
(decimal: Nat)
: problem_spec implementation decimal
:= by
  use implementation decimal
  constructor
  · rfl
  · unfold implementation problem_spec
    let binaryDigits := natToBinary decimal
    let binaryString := listNatToString binaryDigits
    constructor
    · -- 4 < result.length
      have h1 : binaryString.length > 0 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      rw [String.length_append, String.length_append]
      have : ("db" : String).length = 2 := by simp
      rw [this]
      omega
    constructor
    · -- result.drop (result.length - 2) = "db"
      rw [String.length_append, String.length_append]
      have h1 : binaryString.length > 0 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      have db_len : ("db" : String).length = 2 := by simp
      rw [db_len]
      have h2 : 2 + binaryString.length + 2 - 2 = 2 + binaryString.length := by omega
      rw [h2]
      rw [String.drop_append_of_le_length]
      rw [String.drop_append]
      simp
      simp [db_len]
    constructor
    · -- result.take 2 = "db"
      rw [String.take_append_of_le_length]
      simp
      simp
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      have h_eq : (("db" ++ binaryString ++ "db").toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat) = binaryDigits := by
        rw [String.toList_append, String.toList_append]
        rw [List.drop_append_of_le_length]
        rw [List.dropLast_append]
        rw [List.dropLast_append]
        rw [listNatToString_map_inv]
        exact natToBinary_binary_digits decimal
        rw [String.toList]
        simp
        rw [String.toList]
        simp
        simp [String.toList]
      rw [h_eq]
      rw [natToBinary_correct]