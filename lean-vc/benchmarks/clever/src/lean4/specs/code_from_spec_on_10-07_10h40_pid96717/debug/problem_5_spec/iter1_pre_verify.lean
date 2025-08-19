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
  | xs => 
    let rec go : List Int → List Int
      | [] => []
      | [x] => [x]
      | x :: xs => x :: delimeter :: go xs
    go xs

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
lemma intersperse_cons_cons (delimeter: Int) (x y: Int) (xs: List Int) :
  intersperse delimeter (x :: y :: xs) = 
  x :: delimeter :: intersperse delimeter (y :: xs) := by
  simp [intersperse]
  sorry

-- LLM HELPER
lemma intersperse_length (delimeter: Int) (xs: List Int) :
  xs.length = 0 → (intersperse delimeter xs).length = 0 ∧
  xs.length = 1 → (intersperse delimeter xs).length = 2 ∧
  xs.length ≥ 2 → (intersperse delimeter xs).length = 2 * xs.length - 1 := by
  sorry

-- LLM HELPER
lemma intersperse_get (delimeter: Int) (xs: List Int) (i: Nat) :
  i < xs.length →
  (intersperse delimeter xs)[2 * i]! = xs[i]! ∧
  (0 < 2*i - 1 → (intersperse delimeter xs)[2 * i - 1]! = delimeter) := by
  sorry

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter := by
  simp [problem_spec, implementation]
  use intersperse delimeter numbers
  constructor
  · rfl
  · cases' numbers with hd tl
    · left
      constructor
      · simp [intersperse_nil]
      · simp [intersperse_nil]
    · cases' tl with hd2 tl2
      · right
        left
        constructor
        · simp [intersperse_singleton]
        · constructor
          · simp
          · constructor
            · simp [intersperse_singleton]
            · simp [intersperse_singleton]
      · right
        right
        constructor
        · have h: (hd :: hd2 :: tl2).length ≥ 2 := by simp
          have h_len := intersperse_length delimeter (hd :: hd2 :: tl2)
          simp at h_len
          exact h_len.2.2 h
        · intro i hi
          exact intersperse_get delimeter (hd :: hd2 :: tl2) i hi