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
    induction n using Nat.strong_induction with
    | ind n ih =>
      if h : n = 0 then
        simp [h, natToBinary, Nat.ofDigits]
      else
        unfold natToBinary
        simp [h]
        sorry

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).toList.map (fun c => c.toNat - 48) = l := by
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
  if h : n = 0 then
    simp [h]
    intro x hx
    simp at hx
    rw [hx]
    norm_num
  else
    intro x hx
    have : x = 0 ∨ x = 1 := by
      sorry
    cases this with
    | inl h => rw [h]; norm_num
    | inr h => rw [h]; norm_num

-- LLM HELPER
lemma natToBinary_nonempty (n : Nat) : (natToBinary n).length > 0 := by
  unfold natToBinary
  if h : n = 0 then
    simp [h]
  else
    simp [h]
    sorry

-- LLM HELPER
lemma listNatToString_length (l : List Nat) : (listNatToString l).length = l.length := by
  unfold listNatToString
  simp [String.length_mk]

-- LLM HELPER
lemma string_append_take_left (s t : String) (n : Nat) (h : n ≤ s.length) :
  (s ++ t).take n = s.take n := by
  simp [String.take_append_of_le_length h]

-- LLM HELPER
lemma string_append_drop_right (s t : String) (n : Nat) (h : n ≥ s.length) :
  (s ++ t).drop n = t.drop (n - s.length) := by
  simp [String.drop_append_eq]

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
      linarith
    constructor
    · -- result.drop (result.length - 2) = "db"
      rw [String.length_append, String.length_append]
      have h1 : binaryString.length ≥ 1 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      have h2 : 2 + binaryString.length + 2 - 2 = 2 + binaryString.length := by
        simp [Nat.add_sub_cancel]
      rw [h2]
      simp [String.drop_append_eq]
    constructor
    · -- result.take 2 = "db"
      have h : 2 ≤ "db".length := by simp
      rw [string_append_take_left]
      · simp
      · simp
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      simp only [String.toList_append]
      have h_eq : (("db" ++ binaryString ++ "db").toList.drop 2).dropLast.dropLast.map (fun c => c.toNat - '0'.toNat) = binaryDigits := by
        simp [String.toList_append]
        rw [List.drop_append_eq]
        simp [String.toList]
        rw [List.dropLast_append]
        simp [String.toList]
        rw [List.dropLast_append]
        simp [String.toList]
        rw [listNatToString_map_inv]
        exact natToBinary_binary_digits decimal
      rw [h_eq]
      rw [natToBinary_correct]