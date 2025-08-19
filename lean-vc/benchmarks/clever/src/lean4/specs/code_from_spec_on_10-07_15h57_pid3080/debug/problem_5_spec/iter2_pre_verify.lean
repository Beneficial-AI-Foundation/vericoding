import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def intersperse (numbers: List Int) (delimeter: Int) : List Int :=
  match numbers with
  | [] => []
  | [x] => [x, delimeter]
  | x :: xs => x :: delimeter :: intersperse xs delimeter

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
  | _ => intersperse numbers delimeter

-- LLM HELPER
lemma intersperse_length (numbers: List Int) (delimeter: Int) : 
  numbers.length ≥ 2 → (intersperse numbers delimeter).length = 2 * numbers.length - 1 := by
  intro h
  induction numbers with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => simp [intersperse] at h; omega
    | cons y ys =>
      simp [intersperse]
      have : (x :: y :: ys).length ≥ 2 := by simp; omega
      have : (y :: ys).length ≥ 1 := by simp; omega
      rw [List.length_cons, List.length_cons]
      simp [intersperse]
      omega

-- LLM HELPER
lemma intersperse_indexing (numbers: List Int) (delimeter: Int) :
  numbers.length ≥ 2 →
  ∀ i, i < numbers.length →
  (intersperse numbers delimeter)[2 * i]! = numbers[i]! ∧
  (0 < 2*i - 1 → (intersperse numbers delimeter)[2 * i - 1]! = delimeter) := by
  intro h i hi
  induction numbers generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => 
      simp [intersperse]
      cases xs with
      | nil => simp at h; omega
      | cons y ys => simp [intersperse]
    | succ n =>
      cases xs with
      | nil => simp at hi; omega
      | cons y ys =>
        simp [intersperse]
        have : (y :: ys).length ≥ 1 := by simp; omega
        have hn : n < (y :: ys).length := by simp at hi; omega
        simp [List.getElem_cons_succ]
        constructor
        · rw [List.getElem_cons_succ]
          simp [intersperse]
          omega
        · intro h_pos
          simp [intersperse]
          omega

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  simp [problem_spec]
  use implementation numbers delimeter
  constructor
  · rfl
  · simp [implementation]
    cases numbers with
    | nil => 
      left
      simp
    | cons x xs =>
      cases xs with
      | nil =>
        right
        left
        simp
      | cons y ys =>
        right
        right
        constructor
        · simp [intersperse]
          apply intersperse_length
          simp
          omega
        · apply intersperse_indexing
          simp
          omega