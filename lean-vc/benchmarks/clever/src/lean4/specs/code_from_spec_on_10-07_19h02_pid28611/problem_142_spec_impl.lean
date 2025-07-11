import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst : List Int) :=
-- spec
let spec (result : Int) :=
let last := lst.length-1;
(lst = [] → result = 0) ∧
(lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + impl (lst.take last)) ∧
(lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + impl (lst.take last))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma list_take_length_lt (lst : List Int) (h : lst ≠ []) : 
  (lst.take (lst.length - 1)).length < lst.length := by
  cases lst with
  | nil => contradiction
  | cons head tail =>
    simp [List.take, List.length_cons]
    omega

def implementation (lst : List Int) : Int := 
  match lst with
  | [] => 0
  | _ => 
    let last := lst.length - 1
    let lastElem := lst[last]!
    if last % 3 = 0 then
      lastElem ^ 2 + implementation (lst.take last)
    else if last % 4 = 0 then
      lastElem ^ 3 + implementation (lst.take last)
    else
      lastElem + implementation (lst.take last)
termination_by lst.length
decreasing_by
  simp_wf
  apply list_take_length_lt
  exact List.ne_nil_of_length_pos (by omega)

-- LLM HELPER
lemma implementation_nil : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (head : Int) (tail : List Int) :
  let last := tail.length
  let lastElem := (head :: tail)[last]!
  implementation (head :: tail) = 
    if last % 3 = 0 then
      lastElem ^ 2 + implementation ((head :: tail).take last)
    else if last % 4 = 0 then
      lastElem ^ 3 + implementation ((head :: tail).take last)
    else
      lastElem + implementation ((head :: tail).take last) := by
  simp [implementation, List.length_cons]

-- LLM HELPER
lemma cons_getelem_length (head : Int) (tail : List Int) :
  (head :: tail)[tail.length]! = head := by
  cases tail with
  | nil => simp [List.getElem!_cons_zero]
  | cons h t => 
    simp [List.getElem!_cons_succ]
    rw [List.getElem!_cons_succ]
    simp [Nat.succ_sub_succ_eq_sub]

-- LLM HELPER
lemma cons_take_length (head : Int) (tail : List Int) :
  (head :: tail).take tail.length = tail := by
  simp [List.take_cons]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · simp [problem_spec]
    cases lst with
    | nil => 
      constructor
      · intro h
        exact implementation_nil
      · constructor
        · intro h1 h2
          simp at h1
        · constructor
          · intro h1 h2 h3
            simp at h1
          · intro h1 h2 h3
            simp at h1
    | cons head tail =>
      simp [List.length_cons]
      constructor
      · intro h
        contradiction
      · constructor
        · intro h1 h2
          rw [implementation_cons]
          simp [h2]
          rw [cons_getelem_length, cons_take_length]
        · constructor
          · intro h1 h2 h3
            rw [implementation_cons]
            simp [h2, h3]
            rw [cons_getelem_length, cons_take_length]
          · intro h1 h2 h3
            rw [implementation_cons]
            simp [h2, h3]
            rw [cons_getelem_length, cons_take_length]