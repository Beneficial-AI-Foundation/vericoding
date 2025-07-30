import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List String → List String)
-- inputs
(lst: List String) :=
-- spec
let spec (result : List String) :=
  lst.all (fun s => s.data.all (fun c => c.isDigit)) →
  (result.length = 0 ↔ lst.length = 0) ∧
  (result.length > 0 →
  let num_odd_digits := (lst.head!.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  result.head! = "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  ∧ result.tail! = implementation lst.tail!)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List String) : List String := 
  match lst with
  | [] => []
  | h :: t => 
    let num_odd_digits := (h.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
    let result_str := "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
    result_str :: implementation t

-- LLM HELPER
lemma implementation_empty : implementation [] = [] := by
  rfl

-- LLM HELPER
lemma implementation_cons (h : String) (t : List String) : 
  implementation (h :: t) = 
  let num_odd_digits := (h.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  let result_str := "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  result_str :: implementation t := by
  rfl

-- LLM HELPER
lemma implementation_length_zero_iff (lst : List String) : 
  (implementation lst).length = 0 ↔ lst.length = 0 := by
  cases lst with
  | nil => simp [implementation_empty]
  | cons h t => simp [implementation_cons]

-- LLM HELPER
lemma implementation_head_tail (lst : List String) (h : lst.length > 0) :
  let result := implementation lst
  result.length > 0 ∧
  let num_odd_digits := (lst.head!.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length
  result.head! = "the number of odd elements " ++ num_odd_digits.repr ++ "n the str" ++ num_odd_digits.repr ++ "ng " ++ num_odd_digits.repr ++ " of the " ++ num_odd_digits.repr ++ "nput."
  ∧ result.tail! = implementation lst.tail! := by
  cases lst with
  | nil => simp at h
  | cons head tail => 
    simp [implementation_cons]
    constructor
    · simp
    constructor
    · rfl
    · simp [List.tail!]

theorem correctness
(lst: List String)
: problem_spec implementation lst
:= by
  use implementation lst
  constructor
  · rfl
  · intro h
    constructor
    · exact implementation_length_zero_iff lst
    · intro pos
      have list_pos : lst.length > 0 := by
        rw [← implementation_length_zero_iff]
        exact pos
      exact implementation_head_tail lst list_pos