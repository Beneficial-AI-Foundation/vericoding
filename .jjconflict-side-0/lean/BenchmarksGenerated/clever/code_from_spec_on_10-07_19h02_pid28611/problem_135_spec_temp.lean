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
(arr: List Int) :=
-- spec
let spec (result: Int) :=
  ¬arr.any (fun x => 1 < arr.count x) →
  (arr.length = 0 ∨ arr.length = 1 → result = -1) ∧
  (1 < arr.length →
    let last := arr.length-1;
    let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
    result = max (impl (arr.take last)) i);
-- program termination
∃ result, impl arr = result ∧
-- return value satisfies spec
spec result

def implementation (arr: List Int) : Int :=
  if arr.length = 0 ∨ arr.length = 1 then
    -1
  else
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i
termination_by arr.length
decreasing_by
  simp_wf
  rw [List.length_take]
  simp only [min_def]
  split_ifs with h
  · have h_pos : 0 < arr.length := by
      have h_not_short : ¬(arr.length = 0 ∨ arr.length = 1) := by assumption
      push_neg at h_not_short
      cases' arr.length with n
      · exact absurd rfl h_not_short.1
      · cases' n with m
        · exact absurd rfl h_not_short.2
        · exact Nat.succ_pos _
    have h_last_pos : 0 < arr.length - 1 := by
      cases' arr.length with n
      · exact absurd rfl (by assumption : ¬(arr.length = 0 ∨ arr.length = 1)).1
      · cases' n with m
        · exact absurd rfl (by assumption : ¬(arr.length = 0 ∨ arr.length = 1)).2
        · simp only [Nat.succ_sub_succ_eq_sub, tsub_zero]
          exact Nat.succ_pos _
    omega
  · have h_pos : 0 < arr.length := by
      have h_not_short : ¬(arr.length = 0 ∨ arr.length = 1) := by assumption
      push_neg at h_not_short
      cases' arr.length with n
      · exact absurd rfl h_not_short.1
      · cases' n with m
        · exact absurd rfl h_not_short.2
        · exact Nat.succ_pos _
    omega

-- LLM HELPER
theorem implementation_spec_holds (arr: List Int) : 
  ¬arr.any (fun x => 1 < arr.count x) →
  (arr.length = 0 ∨ arr.length = 1 → implementation arr = -1) ∧
  (1 < arr.length →
    let last := arr.length-1;
    let i := if arr[last]! < arr[last-1]! then Int.ofNat last else -1;
    implementation arr = max (implementation (arr.take last)) i) := by
  intro h_no_duplicates
  constructor
  · intro h_short
    simp only [implementation, h_short, if_true]
  · intro h_long
    simp only [implementation]
    have h_not_short : ¬(arr.length = 0 ∨ arr.length = 1) := by
      push_neg
      constructor
      · cases' arr.length with n
        · norm_num at h_long
        · exact Nat.succ_ne_zero n
      · cases' arr.length with n
        · norm_num at h_long
        · cases' n with m
          · norm_num at h_long
          · norm_num
    simp only [h_not_short, if_false]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · exact implementation_spec_holds arr