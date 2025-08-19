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

-- LLM HELPER
def intersperse (delimeter: Int) : List Int → List Int
  | [] => []
  | [x] => [x, delimeter]
  | x :: xs => x :: delimeter :: intersperse delimeter xs

def implementation (numbers: List Int) (delimeter: Int) : List Int := 
  intersperse delimeter numbers

-- LLM HELPER
lemma intersperse_nil (delimeter: Int) : intersperse delimeter [] = [] := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_singleton (delimeter: Int) (x: Int) : 
  intersperse delimeter [x] = [x, delimeter] := by
  simp [intersperse]

-- LLM HELPER
lemma intersperse_cons_cons (delimeter: Int) (x: Int) (xs: List Int) :
  intersperse delimeter (x :: xs) = 
  x :: delimeter :: intersperse delimeter xs := by
  cases xs with
  | nil => simp [intersperse]
  | cons y ys => simp [intersperse]

-- LLM HELPER
lemma intersperse_length (delimeter: Int) (xs: List Int) :
  xs.length = 0 → (intersperse delimeter xs).length = 0 := by
  intro h
  cases xs with
  | nil => simp [intersperse]
  | cons x xs => simp at h

-- LLM HELPER
lemma intersperse_length_one (delimeter: Int) (xs: List Int) :
  xs.length = 1 → (intersperse delimeter xs).length = 2 := by
  intro h
  cases xs with
  | nil => simp at h
  | cons x xs => 
    cases xs with
    | nil => simp [intersperse]
    | cons y ys => simp at h

-- LLM HELPER
lemma intersperse_length_ge_two (delimeter: Int) (xs: List Int) :
  xs.length ≥ 2 → (intersperse delimeter xs).length = 2 * xs.length - 1 := by
  intro h
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    cases xs with
    | nil => simp at h
    | cons y ys => 
      simp [intersperse]
      cases ys with
      | nil => simp
      | cons z zs => 
        simp
        have h_ge : (y :: z :: zs).length ≥ 2 := by simp
        have ih_applied := ih h_ge
        simp at ih_applied
        rw [ih_applied]
        simp
        ring

-- LLM HELPER
lemma intersperse_get_even (delimeter: Int) (xs: List Int) (i: Nat) :
  i < xs.length → (intersperse delimeter xs)[2 * i]! = xs[i]! := by
  intro h
  induction xs generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [intersperse]
    | succ i' =>
      cases xs with
      | nil => simp at h
      | cons y ys => 
        simp [intersperse]
        have h' : i' < (y :: ys).length := by simp at h; exact Nat.lt_of_succ_lt h
        have ih_applied := ih h'
        simp at ih_applied
        rw [ih_applied]
        simp

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  simp [problem_spec, implementation]
  use intersperse delimeter numbers
  constructor
  · rfl
  · cases numbers with
    | nil => 
      left
      constructor
      · exact intersperse_length delimeter [] rfl
      · simp [intersperse]
    | cons hd tl =>
      cases tl with
      | nil =>
        right
        left
        constructor
        · exact intersperse_length_one delimeter [hd] rfl
        · constructor
          · simp
          · constructor
            · simp [intersperse]
            · simp [intersperse]
      | cons hd2 tl2 =>
        right
        right
        constructor
        · have h: (hd :: hd2 :: tl2).length ≥ 2 := by simp
          exact intersperse_length_ge_two delimeter (hd :: hd2 :: tl2) h
        · intro i hi
          constructor
          · exact intersperse_get_even delimeter (hd :: hd2 :: tl2) i hi
          · intro h_pos
            induction i with
            | zero => 
              simp at h_pos
            | succ i' =>
              simp [intersperse]
              have h_cases : i' < (hd2 :: tl2).length := by simp at hi; exact Nat.lt_of_succ_lt hi
              cases tl2 with
              | nil => simp [intersperse]
              | cons x xs => simp [intersperse]