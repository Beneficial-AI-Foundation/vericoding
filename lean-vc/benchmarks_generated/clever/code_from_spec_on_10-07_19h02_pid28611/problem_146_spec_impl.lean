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
lemma is_valid_iff (n : Int) : is_valid n = true ↔ (n > 10 ∧ Odd (get_first_digit n) ∧ Odd (get_last_digit n)) := by
  simp [is_valid, Bool.and_eq_true, decide_eq_true_eq]

-- LLM HELPER
lemma get_first_digit_eq (n : Int) : get_first_digit n = (toString n.natAbs).toList[0]!.toNat - Char.toNat '0' := by
  rfl

-- LLM HELPER
lemma get_last_digit_eq (n : Int) : get_last_digit n = n % 10 := by
  rfl

-- LLM HELPER
lemma logic_iff (n : Int) : (10 < n ∧ Odd (get_first_digit n)) ∧ Odd (get_last_digit n) ↔
    10 < n ∧ Odd (get_first_digit n) ∧ Odd (get_last_digit n) := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩

-- LLM HELPER
lemma not_valid_helper (head : Int) (h_gt : head > 10) (h : ¬(head > 10 ∧ Odd (get_first_digit head) ∧ Odd (get_last_digit head))) :
  ¬(Odd (get_first_digit head) ∧ Odd (get_last_digit head)) := by
  intro h_both
  apply h
  exact ⟨h_gt, h_both.1, h_both.2⟩

theorem correctness
(nums: List Int)
: problem_spec implementation nums := by
  use implementation nums
  constructor
  · rfl
  · induction nums with
    | nil => simp [implementation]
    | cons head tail ih =>
      simp [implementation]
      by_cases h : is_valid head
      · simp [h]
        rw [is_valid_iff] at h
        have h1 : head > 10 := h.1
        have h2 : Odd (get_first_digit head) := h.2.1
        have h3 : Odd (get_last_digit head) := h.2.2
        simp [h1]
        rw [get_first_digit_eq] at h2
        rw [get_last_digit_eq] at h3
        rw [logic_iff]
        exact ⟨h1, h2, h3⟩
      · simp [h]
        rw [is_valid_iff] at h
        push_neg at h
        by_cases h_gt : head > 10
        · simp [h_gt]
          have h_rest : ¬(Odd (get_first_digit head) ∧ Odd (get_last_digit head)) := not_valid_helper head h_gt h
          rw [get_first_digit_eq, get_last_digit_eq] at h_rest
          exact h_rest
        · simp [h_gt]