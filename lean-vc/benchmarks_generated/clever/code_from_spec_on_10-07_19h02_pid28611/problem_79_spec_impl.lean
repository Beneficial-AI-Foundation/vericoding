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
        have h_div_zero : n / 2 = 0 ∨ n / 2 ≠ 0 := by
          cases' Nat.lt_or_ge n 2 with h_lt h_ge
          · left
            exact Nat.div_lt_iff_le_iff_le_mul_right (by norm_num) |>.mp h_lt
          · right
            exact Nat.div_ne_zero_of_zero_lt_div (Nat.div_pos h_ge (by norm_num))
        cases h_div_zero with
        | inl h_div_z =>
          rw [natToBinary.helper]
          rw [if_neg h_zero]
          rw [h_div_z]
          rw [natToBinary.helper]
          simp
          have : n < 2 := Nat.lt_two_iff.mpr (Or.inl (Nat.eq_one_of_pos_of_div_eq_zero (Nat.pos_of_ne_zero h_zero) h_div_z))
          interval_cases n
          · contradiction
          · simp [Nat.ofDigits]
        | inr h_div_nz =>
          have ih_div := ih (n / 2) div_lt h_div_nz
          rw [natToBinary.helper]
          rw [if_neg h_zero]
          rw [natToBinary.helper]
          rw [if_neg h_div_nz]
          have helper_eq : natToBinary.helper (n / 2) ((n % 2) :: []) = (n % 2) :: natToBinary.helper (n / 2) [] := by
            rw [natToBinary.helper]
            rw [if_neg h_div_nz]
          rw [helper_eq]
          have : natToBinary.helper (n / 2) [] = natToBinary (n / 2) := by
            rw [natToBinary, if_neg h_div_nz]
          rw [this]
          rw [List.reverse_cons]
          rw [Nat.ofDigits_append, Nat.ofDigits_singleton]
          rw [ih_div]
          rw [← Nat.div_add_mod n 2]
          ring

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).data.map (fun c => c.toNat - 48) = l := by
  unfold listNatToString
  simp [String.mk]
  rw [List.map_map]
  congr 1
  ext x
  have hx : x < 2 := h x (by assumption)
  cases x with
  | zero => simp [Char.ofNat, Char.toNat]
  | succ n => 
    cases n with
    | zero => simp [Char.ofNat, Char.toNat]
    | succ m => exfalso; omega

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
    have : ∀ m acc, ∀ x ∈ natToBinary.helper m acc, (x < 2 ∨ x ∈ acc) := by
      intro m
      induction m using Nat.strong_induction_on with
      | h m ih =>
        intro acc x hx
        rw [natToBinary.helper] at hx
        if hm : m = 0 then
          rw [if_pos hm] at hx
          exact Or.inr hx
        else
          rw [if_neg hm] at hx
          have div_lt : m / 2 < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) (by norm_num)
          have ih_result := ih (m / 2) div_lt ((m % 2) :: acc) x hx
          cases ih_result with
          | inl h => exact Or.inl h
          | inr h => 
            cases h with
            | head => exact Or.inl (Nat.mod_two_eq_zero_or_one m |>.elim (fun h => by rw [h]; norm_num) (fun h => by rw [h]; norm_num))
            | tail h => exact Or.inr h
    have result := this n [] x hx
    cases result with
    | inl h => exact h
    | inr h => exact absurd h (List.not_mem_nil x)

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
          simp [List.length_cons]
    exact this n [] (Nat.pos_of_ne_zero h)

-- LLM HELPER
lemma listNatToString_length (l : List Nat) : (listNatToString l).length = l.length := by
  unfold listNatToString
  rw [String.length_mk]
  rw [List.length_map]

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
      rw [String.drop_append, String.drop_append]
      simp
    constructor
    · -- result.take 2 = "db"
      rw [String.take_append]
      simp
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      have h_eq : (("db" ++ binaryString ++ "db").toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat) = binaryDigits := by
        rw [String.toList_append, String.toList_append]
        rw [List.drop_append, List.drop_append]
        rw [List.dropLast_append, List.dropLast_append]
        rw [listNatToString_map_inv]
        exact natToBinary_binary_digits decimal
        simp
        simp
        simp
      rw [h_eq]
      exact natToBinary_correct decimal