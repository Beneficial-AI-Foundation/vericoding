import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → List Int)
(numbers: List Int)
(delimeter: Int) :=
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 2 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]! ∧ result[1]! = delimeter) ∨
(result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter));
∃ result, implementation numbers delimeter = result ∧
spec result

def implementation (numbers: List Int) (delimeter: Int) : List Int := 
match numbers with
| [] => []
| [x] => [x, delimeter]
| x :: xs => x :: delimeter :: implementation xs delimeter

-- LLM HELPER
lemma implementation_length_empty : 
  ∀ delimeter, (implementation [] delimeter).length = 0 := by
  intro delimeter
  rfl

-- LLM HELPER
lemma implementation_length_singleton :
  ∀ x delimeter, (implementation [x] delimeter).length = 2 := by
  intro x delimeter
  rfl

-- LLM HELPER
lemma implementation_length_cons :
  ∀ x xs delimeter, xs ≠ [] → 
  (implementation (x :: xs) delimeter).length = 2 + (implementation xs delimeter).length := by
  intro x xs delimeter h
  cases xs with
  | nil => contradiction
  | cons y ys => 
    simp only [implementation]
    simp [List.length_cons]
    omega

-- LLM HELPER
lemma implementation_getElem_even :
  ∀ numbers delimeter i, i < numbers.length →
  (implementation numbers delimeter)[2 * i]! = numbers[i]! := by
  intro numbers delimeter i hi
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => 
      simp only [implementation]
      cases xs with
      | nil => simp [List.getElem_cons_zero]
      | cons y ys => simp [List.getElem_cons_zero]
    | succ j =>
      cases xs with
      | nil => simp at hi; omega
      | cons y ys =>
        simp only [implementation]
        have this : j < (y :: ys).length := by simp at hi; omega
        have ih_applied := ih this
        simp [Nat.succ_mul, List.getElem_cons_succ]
        exact ih_applied

-- LLM HELPER  
lemma implementation_getElem_odd :
  ∀ numbers delimeter i, i < numbers.length → 0 < 2*i - 1 →
  (implementation numbers delimeter)[2 * i - 1]! = delimeter := by
  intro numbers delimeter i hi hpos
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp at hpos
    | succ j =>
      cases xs with
      | nil => simp at hi; omega
      | cons y ys =>
        simp only [implementation]
        have this : j < (y :: ys).length := by simp at hi; omega
        have hpos_j : 0 < 2 * j - 1 := by omega
        have ih_applied := ih this hpos_j
        simp [Nat.succ_mul, List.getElem_cons_succ]
        exact ih_applied

-- LLM HELPER
lemma implementation_length_general :
  ∀ numbers delimeter, numbers.length ≥ 2 →
  (implementation numbers delimeter).length = 2 * numbers.length - 1 := by
  intro numbers delimeter h
  induction numbers with
  | nil => simp at h
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys =>
      rw [implementation_length_cons]
      · cases ys with
        | nil => 
          simp [implementation]
          omega
        | cons z zs =>
          have this : (y :: z :: zs).length ≥ 2 := by simp; omega
          rw [implementation_length_general (y :: z :: zs) delimeter this]
          simp
          omega
      · simp

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  use implementation numbers delimeter
  constructor
  · rfl
  · cases numbers with
    | nil => 
      left
      constructor
      · exact implementation_length_empty delimeter
      · rfl
    | cons x xs =>
      cases xs with
      | nil =>
        right
        left
        constructor
        · exact implementation_length_singleton x delimeter
        · constructor
          · simp
          · constructor
            · simp [implementation]
            · simp [implementation]
      | cons y ys =>
        right
        right
        constructor
        · rw [implementation_length_general]
          simp; omega
        · intro i hi
          constructor
          · exact implementation_getElem_even (x :: y :: ys) delimeter i hi
          · intro hpos
            exact implementation_getElem_odd (x :: y :: ys) delimeter i hi hpos