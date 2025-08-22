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
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst != [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (impl (lst.drop 1) = (result - lst[0]!.ceil^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Rat) : Int :=
  match lst with
  | [] => 0
  | hd :: tl => (implementation tl) + hd.ceil^2

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (hd : Rat) (tl : List Rat) : 
  implementation (hd :: tl) = implementation tl + hd.ceil^2 := by
  simp [implementation]

-- LLM HELPER
lemma list_drop_cons (hd : Rat) (tl : List Rat) : 
  (hd :: tl).drop 1 = tl := by
  simp [List.drop]

-- LLM HELPER
lemma list_head_cons (hd : Rat) (tl : List Rat) : 
  (hd :: tl)[0]! = hd := by
  simp [List.get!]

-- LLM HELPER
lemma list_ne_empty_cons (hd : Rat) (tl : List Rat) : 
  hd :: tl ≠ [] := by
  simp

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  simp [problem_spec]
  let spec (result: Int) :=
    (lst = [] → result = 0) ∧
    (lst ≠ [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (implementation (lst.drop 1) = (result - lst[0]!.ceil^2)))
  
  use implementation lst
  constructor
  · rfl
  · simp [spec]
    cases' lst with hd tl
    · left
      simp [implementation_empty]
    · right
      constructor
      · simp [list_ne_empty_cons]
      · constructor
        · rw [implementation_cons, list_head_cons]
          simp [Int.add_sub_cancel]
        · rw [list_drop_cons, list_head_cons, implementation_cons]
          simp [Int.add_sub_cancel]