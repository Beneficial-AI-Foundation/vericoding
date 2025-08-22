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
    simp [List.take]
    rw [List.length_cons]
    simp [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
    rw [List.length_take]
    simp [min_def]
    split_ifs with h1
    · exact Nat.lt_succ_self _
    · have : tail.length ≥ tail.length := le_refl _
      rw [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] at h1
      push_neg at h1
      have : tail.length = 0 := Nat.eq_zero_of_le_zero h1
      rw [this]
      exact Nat.zero_lt_succ _

-- LLM HELPER
lemma implementation_spec_helper (lst : List Int) : 
  let spec (result : Int) :=
    let last := lst.length-1;
    (lst = [] → result = 0) ∧
    (lst ≠ [] ∧ last % 3 = 0 → result = lst[last]! ^ 2 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 4 = 0 ∧ last % 3 != 0 → result = lst[last]! ^ 3 + implementation (lst.take last)) ∧
    (lst ≠ [] ∧ last % 3 != 0 ∧ last % 4 != 0 → result = lst[last]! + implementation (lst.take last))
  spec (implementation lst) := by
  simp [implementation]
  cases lst with
  | nil => simp
  | cons head tail =>
    simp
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h1, h2]

theorem correctness
(lst : List Int)
: problem_spec implementation lst := by
  use implementation lst
  constructor
  · rfl
  · exact implementation_spec_helper lst