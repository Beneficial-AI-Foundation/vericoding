import Mathlib
-- <vc-preamble>

def ValidInput (n k : Int) (numbers : List Int) : Prop :=
  n ≥ 1 ∧ k ≥ 0 ∧ numbers.length = n ∧ ∀ i, 0 ≤ i ∧ i < numbers.length → numbers[i]! > 0

def countLuckyDigits (num : Int) : Int :=
  if h : num ≥ 0 then
    if num = 0 then 0
    else
      let digit := num % 10
      let rest := num / 10
      let digitCount := if digit = 4 ∨ digit = 7 then 1 else 0
      digitCount + countLuckyDigits rest
  else 0
termination_by num.natAbs

def countValidNumbers (numbers : List Int) (k : Int) (upTo : Nat) : Int :=
  if upTo = 0 then 0
  else
    let prevCount := countValidNumbers numbers k (upTo - 1)
    if h : upTo - 1 < numbers.length then
      if countLuckyDigits numbers[upTo - 1]! ≤ k then prevCount + 1 else prevCount
    else prevCount

@[reducible, simp]
def solve_precond (n k : Int) (numbers : List Int) : Prop :=
  ValidInput n k numbers
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: Helper lemmas for working with List.filter and length conversions
lemma list_filter_length_nonneg {α : Type*} (l : List α) (p : α → Bool) : 
  0 ≤ (l.filter p).length := Nat.zero_le _

lemma list_filter_length_le {α : Type*} (l : List α) (p : α → Bool) : 
  (l.filter p).length ≤ l.length := List.length_filter_le _ _

lemma int_coe_list_length {α : Type*} (l : List α) : 
  (0 : Int) ≤ l.length := Nat.cast_nonneg _

-- Fixed: Direct coercion inequality lemma
lemma int_coe_filter_length_le {α : Type*} (l : List α) (p : α → Bool) : 
  (↑(l.filter p).length : Int) ≤ (↑l.length : Int) := by
  simp [Nat.cast_le]
  exact List.length_filter_le _ _
-- </vc-helpers>

-- <vc-definitions>
def solve (n k : Int) (numbers : List Int) (h_precond : solve_precond n k numbers) : Int :=
  ↑(numbers.filter (fun num => countLuckyDigits num ≤ k)).length
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (n k : Int) (numbers : List Int) (result : Int) (h_precond : solve_precond n k numbers) : Prop :=
  0 ≤ result ∧ result ≤ n ∧ result = (numbers.filter (fun num => countLuckyDigits num ≤ k)).length

theorem solve_spec_satisfied (n k : Int) (numbers : List Int) (h_precond : solve_precond n k numbers) :
    solve_postcond n k numbers (solve n k numbers h_precond) h_precond := by
  unfold solve solve_postcond
  constructor
  · -- 0 ≤ result
    simp [Nat.cast_nonneg]
  constructor  
  · -- result ≤ n
    have h_valid := h_precond
    unfold solve_precond ValidInput at h_valid
    have h_len : numbers.length = n := h_valid.2.2.1
    rw [← h_len]
    -- Use the corrected coercion lemma
    exact int_coe_filter_length_le numbers (fun num => countLuckyDigits num ≤ k)
  · -- result = (numbers.filter (fun num => countLuckyDigits num ≤ k)).length
    simp
-- </vc-theorems>
