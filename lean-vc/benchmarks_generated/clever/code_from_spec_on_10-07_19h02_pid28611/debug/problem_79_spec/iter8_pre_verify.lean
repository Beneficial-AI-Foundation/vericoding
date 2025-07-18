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
    simp [h, natToBinary, Nat.ofDigits]
  else
    induction n using Nat.strong_induction_on with
    | h n ih =>
      if h_zero : n = 0 then
        simp [h_zero, natToBinary, Nat.ofDigits]
      else
        unfold natToBinary
        simp [h_zero]
        have div_lt : n / 2 < n := Nat.div_lt_self (Nat.pos_of_ne_zero h_zero) (by norm_num)
        have helper_eq : natToBinary.helper n [] = 
          natToBinary.helper (n / 2) ((n % 2) :: []) := by
          simp [natToBinary.helper, h_zero]
        rw [helper_eq]
        have : Nat.ofDigits 2 (natToBinary (n / 2)).reverse = n / 2 := ih (n / 2) div_lt h_zero
        sorry

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).data.map (fun c => c.toNat - 48) = l := by
  unfold listNatToString
  simp only [String.mk, List.map_map]
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
  if h : n = 0 then
    simp [h]
    intro x hx
    simp at hx
    rw [hx]
    norm_num
  else
    intro x hx
    simp [h] at hx
    have : ∀ m acc, ∀ x ∈ natToBinary.helper m acc, x < 2 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro acc x hx
        simp [natToBinary.helper] at hx
        if hm : m = 0 then
          simp [hm] at hx
          exact hx
        else
          simp [hm] at hx
          cases hx with
          | inl h => rw [h]; norm_num
          | inr h => exact ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)) ((m % 2) :: acc) x h
    exact this n [] x hx

-- LLM HELPER
lemma natToBinary_nonempty (n : Nat) : (natToBinary n).length > 0 := by
  unfold natToBinary
  if h : n = 0 then
    simp [h]
  else
    simp [h]
    have : ∀ m acc, (natToBinary.helper m acc).length > 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro acc
        simp [natToBinary.helper]
        if hm : m = 0 then
          simp [hm]
          exact Nat.zero_lt_succ _
        else
          simp [hm]
          exact ih (m / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)) ((m % 2) :: acc)
    exact this n []

-- LLM HELPER
lemma listNatToString_length (l : List Nat) : (listNatToString l).length = l.length := by
  unfold listNatToString
  simp [String.length_mk]

-- LLM HELPER
lemma string_append_take_left (s t : String) (n : Nat) (h : n ≤ s.length) :
  (s ++ t).take n = s.take n := by
  ext i
  if hi : i < n then
    simp [String.get_take, hi]
    if his : i < s.length then
      simp [String.get_append, his]
    else
      exfalso
      exact his (Nat.lt_of_lt_of_le hi h)
  else
    simp [String.get_take, hi]

-- LLM HELPER
lemma string_append_drop_right (s t : String) (n : Nat) :
  (s ++ t).drop n = if n ≤ s.length then (s.drop n) ++ t else t.drop (n - s.length) := by
  ext i
  if hn : n ≤ s.length then
    simp [String.get_drop, hn]
    if his : n + i < s.length then
      simp [String.get_append, his]
    else
      simp [String.get_append, his]
      congr 1
      omega
  else
    simp [String.get_drop, hn]
    congr 1
    omega

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
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      rw [String.length_append, String.length_append]
      simp
      have : ("db" : String).length = 2 := by simp
      rw [this]
      omega
    constructor
    · -- result.drop (result.length - 2) = "db"
      rw [String.length_append, String.length_append]
      have h1 : binaryString.length ≥ 1 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      have db_len : ("db" : String).length = 2 := by simp
      rw [db_len]
      have h2 : 2 + binaryString.length + 2 - 2 = 2 + binaryString.length := by omega
      rw [h2, string_append_drop_right]
      simp [db_len]
      rw [string_append_drop_right]
      simp [db_len]
      have : binaryString.length ≥ 2 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      simp [this]
      rw [Nat.sub_self]
      simp
    constructor
    · -- result.take 2 = "db"
      have h : 2 ≤ ("db" : String).length := by simp
      rw [string_append_take_left]
      · simp
      · simp
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      simp only [String.data_append]
      have h_eq : (("db" ++ binaryString ++ "db").toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat) = binaryDigits := by
        simp [String.toList_append]
        rw [List.drop_append_of_le_length]
        simp [String.toList]
        rw [List.dropLast_append]
        simp [String.toList]
        rw [List.dropLast_append]
        simp [String.toList]
        rw [listNatToString_map_inv]
        exact natToBinary_binary_digits decimal
        simp [String.toList]
        simp [String.toList]
        simp [String.toList]
      rw [h_eq]
      rw [natToBinary_correct]