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
  | h :: t => 
    let (sum_tail, prod_tail) := implementation t
    (h + sum_tail, h * prod_tail)

-- LLM HELPER
lemma implementation_eq_match (numbers: List Int) :
  implementation numbers = match numbers with
  | [] => (0, 1)
  | h :: t => 
    let (sum_tail, prod_tail) := implementation t
    (h + sum_tail, h * prod_tail) := by
  rfl

-- LLM HELPER
lemma implementation_nil : implementation [] = (0, 1) := by
  rfl

-- LLM HELPER
lemma implementation_cons (h : Int) (t : List Int) :
  implementation (h :: t) = 
  let (sum_tail, prod_tail) := implementation t
  (h + sum_tail, h * prod_tail) := by
  rfl

-- LLM HELPER
lemma list_tail_cons (h : Int) (t : List Int) : (h :: t).tail = t := by
  rfl

-- LLM HELPER
lemma list_get_zero_cons (h : Int) (t : List Int) : (h :: t)[0]! = h := by
  rfl

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · intro result h_eq
    rw [← h_eq]
    cases' numbers with h t
    · simp only [implementation_nil]
      constructor
      · intro
        constructor <;> rfl
      · intro h_nonempty
        exact absurd rfl h_nonempty
    · simp only [implementation_cons]
      constructor
      · intro h_empty
        exact absurd rfl h_empty
      · intro h_nonempty
        have h_tail : (h :: t).tail = t := list_tail_cons h t
        have h_get : (h :: t)[0]! = h := list_get_zero_cons h t
        rw [h_tail, h_get]
        constructor
        · simp only [add_sub_cancel']
        · ring