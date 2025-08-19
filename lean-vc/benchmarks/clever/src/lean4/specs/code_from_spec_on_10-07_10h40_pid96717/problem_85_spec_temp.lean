import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
  lst.length = 0 → result = 0 ∧
  lst.length > 0 →
    if lst.length > 1 then
      result = (if Even lst[1]! then lst[1]! else 0) + implementation (lst.drop 2)
    else
      result = (if Even lst[1]! then lst[1]! else 0)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Int) : Int := 
  match lst with
  | [] => 0
  | [x] => if Even x then x else 0
  | x :: y :: rest => (if Even y then y else 0) + implementation rest

-- LLM HELPER
lemma list_length_zero_iff_nil (lst : List Int) : lst.length = 0 ↔ lst = [] := by
  cases lst with
  | nil => simp
  | cons h t => simp

-- LLM HELPER
lemma list_get_first_of_cons (x y : Int) (rest : List Int) : 
  (x :: y :: rest)[1]! = y := by
  simp [List.getElem_cons_succ]

-- LLM HELPER
lemma list_drop_two_of_cons (x y : Int) (rest : List Int) : 
  (x :: y :: rest).drop 2 = rest := by
  simp [List.drop]

-- LLM HELPER
lemma list_get_zero_of_single (x : Int) : [x][1]! = x := by
  simp

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:= by
  unfold problem_spec
  simp only [exists_prop]
  use implementation lst
  constructor
  · rfl
  · intro result h_eq
    rw [← h_eq]
    constructor
    · intro h_empty
      rw [list_length_zero_iff_nil] at h_empty
      rw [h_empty]
      simp [implementation]
    · intro h_nonempty
      cases lst with
      | nil => 
        simp at h_nonempty
      | cons x tail =>
        cases tail with
        | nil =>
          simp [implementation]
          have h_len : (x :: []).length = 1 := by simp
          have h_not_gt : ¬(x :: []).length > 1 := by simp
          rw [if_neg h_not_gt]
          simp
        | cons y rest =>
          simp [implementation]
          have h_len : (x :: y :: rest).length > 1 := by simp [List.length]
          rw [if_pos h_len]
          rw [list_get_first_of_cons, list_drop_two_of_cons]