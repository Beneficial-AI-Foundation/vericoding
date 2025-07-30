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
  sizeOf (lst.take (lst.length - 1)) < sizeOf lst := by
  cases lst with
  | nil => contradiction
  | cons head tail =>
    simp [List.take, List.sizeOf_cons]
    rw [List.length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [List.sizeOf_take]
    have : min tail.length tail.length = tail.length := min_self _
    rw [this]
    simp [List.sizeOf_cons]
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
termination_by lst => sizeOf lst
decreasing_by
  simp_wf
  apply list_take_length_lt
  simp

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
  simp [implementation]
  rw [List.length_cons, Nat.succ_sub_succ_eq_sub, Nat.sub_zero]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · simp [problem_spec]
    cases lst with
    | nil => 
      simp
      exact implementation_nil
    | cons head tail =>
      simp
      constructor
      · intro h
        rw [implementation_cons]
        simp [h]
      · constructor
        · intro h1 h2
          rw [implementation_cons]
          simp [h1, h2]
        · intro h1 h2
          rw [implementation_cons]
          simp [h1, h2]