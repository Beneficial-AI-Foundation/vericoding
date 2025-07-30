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
lemma implementation_empty : implementation [] = (0, 1) := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (h : Int) (t : List Int) : 
  implementation (h :: t) = 
  let (sum_tail, prod_tail) := implementation t
  (h + sum_tail, h * prod_tail) := by
  simp [implementation]

-- LLM HELPER
lemma tail_cons (h : Int) (t : List Int) : (h :: t).tail = t := by
  simp [List.tail]

-- LLM HELPER
lemma head_cons (h : Int) (t : List Int) : (h :: t)[0]! = h := by
  simp [List.get!]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · cases' numbers with h t
    · -- Case: numbers = []
      constructor
      · intro h_empty
        simp [implementation_empty]
      · intro h_ne_empty
        contradiction
    · -- Case: numbers = h :: t
      constructor
      · intro h_empty
        simp at h_empty
      · intro h_ne_empty
        simp [implementation_cons, tail_cons, head_cons]
        let (sum_tail, prod_tail) := implementation t
        constructor
        · ring
        · simp [Prod.fst, Prod.snd]
          ring