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
  | h :: t => h.ceil^2 + implementation t

-- LLM HELPER
lemma implementation_empty : implementation [] = 0 := by
  simp [implementation]

-- LLM HELPER
lemma implementation_cons (h : Rat) (t : List Rat) : 
  implementation (h :: t) = h.ceil^2 + implementation t := by
  simp [implementation]

-- LLM HELPER
lemma list_drop_one_cons (h : Rat) (t : List Rat) : 
  (h :: t).drop 1 = t := by
  simp [List.drop]

-- LLM HELPER
lemma list_head_cons (h : Rat) (t : List Rat) : 
  (h :: t)[0]! = h := by
  simp [List.get!]

-- LLM HELPER
lemma list_nonempty_iff_ne_nil (lst : List Rat) : 
  lst ≠ [] ↔ lst.length > 0 := by
  simp [List.length_pos_iff_ne_nil]

theorem correctness
(lst: List Rat)
: problem_spec implementation lst := by
  simp [problem_spec]
  use implementation lst
  constructor
  · rfl
  · simp
    constructor
    · intro h
      rw [h]
      simp [implementation_empty]
    · intro h
      cases' lst with head tail
      · contradiction
      · simp [implementation_cons, list_head_cons, list_drop_one_cons]
        ring