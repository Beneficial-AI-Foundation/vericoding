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
    let lastElem := lst[last]!
    if last % 3 = 0 then
      lastElem ^ 2 + implementation (lst.take last)
    else if last % 4 = 0 then
      lastElem ^ 3 + implementation (lst.take last)
    else
      lastElem + implementation (lst.take last)

-- LLM HELPER
lemma list_take_length_lt (lst : List Int) (h : lst ≠ []) : (lst.take (lst.length - 1)).length < lst.length := by
  cases lst with
  | nil => contradiction
  | cons head tail =>
    simp [List.take, List.length]
    cases tail with
    | nil => simp
    | cons _ _ => 
      simp [List.length]
      omega

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  unfold problem_spec
  let spec (result : Int) :=
    let last := lst.length-1;
    (lst = [] → result = 0) ∧
    (lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + implementation (lst.take last))
  
  use implementation lst
  constructor
  · rfl
  · unfold spec
    cases h : lst with
    | nil => 
      simp [implementation]
      tauto
    | cons head tail =>
      simp [implementation]
      let last := lst.length - 1
      constructor
      · intro h_eq
        simp at h_eq
      · constructor
        · intro h_ne h_mod3
          simp [last]
          split_ifs with h_if
          · rfl
          · contradiction
        · constructor
          · intro h_ne h_mod4 h_not_mod3
            simp [last]
            split_ifs with h_if1 h_if2
            · contradiction
            · rfl
            · contradiction
          · intro h_ne h_not_mod3 h_not_mod4
            simp [last]
            split_ifs with h_if1 h_if2
            · contradiction
            · contradiction
            · rfl