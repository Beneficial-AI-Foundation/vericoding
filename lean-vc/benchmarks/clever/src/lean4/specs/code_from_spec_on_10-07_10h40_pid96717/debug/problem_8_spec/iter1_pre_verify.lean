import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → (Int × Int))
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: (Int × Int)) :=
let (sum, prod) := result;
(numbers = [] → sum = 0 ∧ prod = 1) ∧
(numbers ≠ [] →
(let (sum_tail, prod_tail) := implementation numbers.tail;
sum - sum_tail = numbers[0]! ∧
sum_tail * prod_tail + prod = sum * prod_tail));
-- program termination
∃ result, implementation numbers = result ∧
spec result

def implementation (numbers: List Int) : (Int × Int) := 
  match numbers with
  | [] => (0, 1)
  | head :: tail => 
    let (sum_tail, prod_tail) := implementation tail
    (head + sum_tail, head * prod_tail)

-- LLM HELPER
lemma implementation_empty : implementation [] = (0, 1) := by
  rfl

-- LLM HELPER
lemma implementation_cons (head : Int) (tail : List Int) : 
  implementation (head :: tail) = 
  let (sum_tail, prod_tail) := implementation tail
  (head + sum_tail, head * prod_tail) := by
  rfl

-- LLM HELPER
lemma get_zero_cons (head : Int) (tail : List Int) : 
  (head :: tail)[0]! = head := by
  rfl

-- LLM HELPER
lemma tail_cons (head : Int) (tail : List Int) : 
  (head :: tail).tail = tail := by
  rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  let spec := fun (result: (Int × Int)) =>
    let (sum, prod) := result;
    (numbers = [] → sum = 0 ∧ prod = 1) ∧
    (numbers ≠ [] →
    (let (sum_tail, prod_tail) := implementation numbers.tail;
    sum - sum_tail = numbers[0]! ∧
    sum_tail * prod_tail + prod = sum * prod_tail))
  
  use implementation numbers
  constructor
  · rfl
  · cases' numbers with head tail
    · -- Case: numbers = []
      simp [implementation_empty]
      constructor
      · intro h
        constructor <;> rfl
      · intro h
        contradiction
    · -- Case: numbers = head :: tail
      simp [implementation_cons, get_zero_cons, tail_cons]
      constructor
      · intro h
        contradiction
      · intro h
        let (sum_tail, prod_tail) := implementation tail
        simp [implementation_cons]
        constructor
        · ring
        · ring