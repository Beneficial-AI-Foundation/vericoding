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

-- LLM HELPER
def count_odd_digits (s : String) : Nat :=
  (s.data.filter (fun c => c.isDigit ∧ c.toNat % 2 = 1)).length

-- LLM HELPER
def make_result_string (n : Nat) : String :=
  "the number of odd elements " ++ n.repr ++ "n the str" ++ n.repr ++ "ng " ++ n.repr ++ " of the " ++ n.repr ++ "nput."

def implementation (lst: List String) : List String := 
  match lst with
  | [] => []
  | head :: tail => 
    let num_odd := count_odd_digits head
    make_result_string num_odd :: implementation tail

-- LLM HELPER
lemma implementation_length (lst : List String) : (implementation lst).length = lst.length := by
  induction lst with
  | nil => simp [implementation]
  | cons h t ih => simp [implementation, ih]

-- LLM HELPER
lemma implementation_head (lst : List String) (h : lst.length > 0) : 
  (implementation lst).head! = make_result_string (count_odd_digits lst.head!) := by
  cases lst with
  | nil => simp at h
  | cons head tail => simp [implementation, List.head!]

-- LLM HELPER
lemma implementation_tail (lst : List String) (h : lst.length > 0) : 
  (implementation lst).tail! = implementation lst.tail! := by
  cases lst with
  | nil => simp at h
  | cons head tail => simp [implementation, List.tail!]

-- LLM HELPER
lemma implementation_empty_iff (lst : List String) : 
  (implementation lst).length = 0 ↔ lst.length = 0 := by
  rw [implementation_length]

theorem correctness
(lst: List String)
: problem_spec implementation lst
:= by
  unfold problem_spec
  use implementation lst
  constructor
  · rfl
  · intro h_all_digits
    constructor
    · exact implementation_empty_iff lst
    · intro h_pos
      constructor
      · rw [implementation_head lst h_pos]
        simp [make_result_string, count_odd_digits]
      · exact implementation_tail lst h_pos