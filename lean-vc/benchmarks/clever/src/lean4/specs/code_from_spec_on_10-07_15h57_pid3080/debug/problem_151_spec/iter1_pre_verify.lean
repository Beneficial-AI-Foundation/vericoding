import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(numbers: List Rat) :=
let isEven (n : Rat) := n % 2 = 0;
let isNegative (n : Rat) := n < 0;
let isNotInteger (n : Rat) := ¬ n.isInt;
-- spec
let spec (result: Int) :=
0 < numbers.length →
0 ≤ result ∧
if numbers.length = 1
then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + impl numbers.tail
-- program terminates
∃ result, impl numbers = result ∧
-- return value satisfies spec
spec result

def implementation (numbers: List Rat) : Int := 
  match numbers with
  | [] => 0
  | [x] => 
    let isEven := x % 2 = 0
    let isNegative := x < 0
    let isNotInteger := ¬ x.isInt
    if isEven ∨ isNegative ∨ isNotInteger then 0 else x.floor ^ 2
  | x :: xs => 
    let isEven := x % 2 = 0
    let isNegative := x < 0
    let isNotInteger := ¬ x.isInt
    if isEven ∨ isNegative ∨ isNotInteger then 0 + implementation xs else x.floor ^ 2 + implementation xs

-- LLM HELPER
lemma implementation_nonneg (numbers: List Rat) : 0 ≤ implementation numbers := by
  induction numbers with
  | nil => simp [implementation]
  | cons x xs ih =>
    simp [implementation]
    split_ifs with h
    · exact add_nonneg (le_refl 0) ih
    · exact add_nonneg (sq_nonneg _) ih

-- LLM HELPER
lemma implementation_single (x: Rat) : 
  implementation [x] = if (x % 2 = 0 ∨ x < 0 ∨ ¬ x.isInt) then 0 else x.floor ^ 2 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (x: Rat) (xs: List Rat) (hxs: xs ≠ []) : 
  implementation (x :: xs) = if (x % 2 = 0 ∨ x < 0 ∨ ¬ x.isInt) then 0 + implementation xs else x.floor ^ 2 + implementation xs := by
  simp [implementation]

-- LLM HELPER
lemma list_length_pos_iff (l: List Rat) : 0 < l.length ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons _ _ => simp

theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers := by
  simp [problem_spec]
  let isEven (n : Rat) := n % 2 = 0
  let isNegative (n : Rat) := n < 0
  let isNotInteger (n : Rat) := ¬ n.isInt
  let spec (result: Int) :=
    0 < numbers.length →
    0 ≤ result ∧
    if numbers.length = 1
    then result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2
    else result = if (isEven numbers[0]! ∨ isNegative numbers[0]! ∨ isNotInteger numbers[0]!) then (0 : Int) else numbers[0]!.floor ^ 2 + implementation numbers.tail
  
  use implementation numbers
  constructor
  · rfl
  · intro h
    constructor
    · exact implementation_nonneg numbers
    · cases numbers with
      | nil => 
        simp at h
      | cons x xs =>
        simp at h
        simp
        cases xs with
        | nil =>
          simp
          rw [implementation_single]
          simp [isEven, isNegative, isNotInteger]
        | cons y ys =>
          simp
          rw [implementation_cons]
          simp [isEven, isNegative, isNotInteger]
          simp [List.tail]
          simp