import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(nums: List Int) :=
-- spec
let spec (result: Int) :=
match nums with
| [] => result = 0
| head::tail =>
  let first_digit := (toString head.natAbs).toList[0]!.toNat - Char.toNat '0';
  let last_digit := head % 10;
  let valid := head > 10 ∧ Odd first_digit ∧ Odd last_digit
  if valid then result = 1 + impl tail else result = impl tail
-- program termination
∃ result, impl nums = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
def get_first_digit (n : Int) : Nat :=
  (toString n.natAbs).toList[0]!.toNat - Char.toNat '0'

-- LLM HELPER
def get_last_digit (n : Int) : Int :=
  n % 10

-- LLM HELPER
def is_valid (n : Int) : Bool :=
  n > 10 && Odd (get_first_digit n) && Odd (get_last_digit n)

def implementation (nums: List Int) : Int :=
  match nums with
  | [] => 0
  | head::tail =>
    if is_valid head then 1 + implementation tail else implementation tail

-- LLM HELPER
lemma get_first_digit_eq (n : Int) : get_first_digit n = (toString n.natAbs).toList[0]!.toNat - Char.toNat '0' := by
  rfl

-- LLM HELPER
lemma get_last_digit_eq (n : Int) : get_last_digit n = n % 10 := by
  rfl

-- LLM HELPER
lemma is_valid_eq (n : Int) : is_valid n = (n > 10 && Odd (get_first_digit n) && Odd (get_last_digit n)) := by
  rfl

-- LLM HELPER
lemma odd_first_digit_conversion (n : Int) : 
  Odd (get_first_digit n) ↔ Odd ((toString n.natAbs).data[0]?.getD 'A').toNat - 48 := by
  simp [get_first_digit]
  rfl

-- LLM HELPER
lemma odd_last_digit_conversion (n : Int) :
  Odd (get_last_digit n) ↔ Odd (n % 10) := by
  simp [get_last_digit]

-- LLM HELPER
lemma implementation_spec (nums : List Int) : 
  let spec (result: Int) :=
    match nums with
    | [] => result = 0
    | head::tail =>
      let first_digit := (toString head.natAbs).toList[0]!.toNat - Char.toNat '0';
      let last_digit := head % 10;
      let valid := head > 10 ∧ Odd first_digit ∧ Odd last_digit
      if valid then result = 1 + implementation tail else result = implementation tail
  spec (implementation nums) := by
  induction nums with
  | nil => simp [implementation]
  | cons head tail ih =>
    simp [implementation]
    by_cases h : is_valid head
    · simp [h]
      rw [is_valid_eq] at h
      simp at h
      have h1 : head > 10 := by
        rw [Bool.and_eq_true] at h
        exact h.1
      have h2 : Odd (get_first_digit head) := by
        rw [Bool.and_eq_true] at h
        exact h.2.1
      have h3 : Odd (get_last_digit head) := by
        rw [Bool.and_eq_true] at h
        exact h.2.2
      simp [h1]
      constructor
      · rw [odd_first_digit_conversion]
        exact h2
      · rw [odd_last_digit_conversion]
        exact h3
    · simp [h]
      rw [is_valid_eq] at h
      simp at h
      rw [Bool.and_eq_false] at h
      cases h with
      | inl h => simp [h]
      | inr h => 
        rw [Bool.and_eq_false] at h
        cases h with
        | inl h => 
          simp [le_refl]
          left
          rw [←odd_first_digit_conversion]
          exact h
        | inr h =>
          simp [le_refl]
          right
          rw [←odd_last_digit_conversion]
          exact h

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  use implementation nums
  constructor
  · rfl
  · exact implementation_spec nums