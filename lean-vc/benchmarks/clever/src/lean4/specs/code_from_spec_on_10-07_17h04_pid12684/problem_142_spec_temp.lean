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

def implementation (lst : List Int) : Int := 
  match lst with
  | [] => 0
  | _ => 
    let last := lst.length - 1
    let lastElement := lst[last]!
    if last % 3 = 0 then
      lastElement ^ 2 + implementation (lst.take last)
    else if last % 4 = 0 then
      lastElement ^ 3 + implementation (lst.take last)
    else
      lastElement + implementation (lst.take last)

-- LLM HELPER
lemma list_take_length_lt (lst : List Int) (h : lst ≠ []) : 
  (lst.take (lst.length - 1)).length < lst.length := by
  cases' lst with hd tl
  · contradiction
  · simp [List.take_length, List.length_cons]
    cases' tl with hd' tl'
    · simp
    · simp [List.length_cons, Nat.min_def]
      split_ifs with h1
      · simp at h1
        omega
      · simp at h1
        omega

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  let spec := fun (result : Int) =>
    let last := lst.length - 1
    (lst = [] → result = 0) ∧
    (lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 ≠ 0 → result = lst[last]! ^ 3 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 3 ≠ 0 ∧ last % 4 ≠ 0 → result = lst[last]! + implementation (lst.take last))
  
  use implementation lst
  constructor
  · rfl
  · unfold spec
    unfold implementation
    cases' lst with hd tl
    · simp
    · simp [List.length_cons]
      split_ifs with h1 h2
      · simp [h1]
      · simp [h1, h2]
      · simp [h1, h2]