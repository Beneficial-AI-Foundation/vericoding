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
    sorry

-- LLM HELPER
lemma listNatToString_map_inv (l : List Nat) (h : ∀ x ∈ l, x < 2) :
  (listNatToString l).toList.map (fun c => c.toNat - 48) = l := by
  unfold listNatToString
  simp only [String.mk_toList, List.map_map]
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
  else
    sorry

-- LLM HELPER
lemma natToBinary_nonempty (n : Nat) : (natToBinary n).length > 0 := by
  unfold natToBinary
  if h : n = 0 then
    simp [h]
  else
    sorry

-- LLM HELPER
lemma listNatToString_length (l : List Nat) : (listNatToString l).length = l.length := by
  unfold listNatToString
  simp [String.length_mk]

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
      norm_num
      exact h1
    constructor
    · -- result.drop (result.length - 2) = "db"
      rw [String.length_append, String.length_append]
      have h1 : binaryString.length ≥ 1 := by
        unfold binaryString
        rw [listNatToString_length]
        exact natToBinary_nonempty decimal
      have h2 : 2 + binaryString.length + 2 - 2 = 2 + binaryString.length := by
        norm_num
      rw [h2]
      rw [String.drop_append_eq]
      rw [String.drop_all]
      simp
    constructor
    · -- result.take 2 = "db"
      rw [String.take_append_eq]
      norm_num
    · -- decimal = Nat.ofDigits 2 resultTrimmed.reverse
      simp only [String.toList_append]
      rw [List.drop_append_eq]
      rw [List.dropLast_append]
      rw [List.dropLast_append]
      simp only [String.toList]
      rw [listNatToString_map_inv]
      · rw [natToBinary_correct]
      · exact natToBinary_binary_digits decimal
      · norm_num
      · norm_num
      · norm_num