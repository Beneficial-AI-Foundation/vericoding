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

-- LLM HELPER
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
  apply List.length_take_le_length

-- LLM HELPER
theorem take_length_lt (arr: List Int) (h: 1 < arr.length) : (arr.take (arr.length - 1)).length < arr.length := by
  rw [List.length_take]
  simp [min_def]
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
    simp [implementation]
    exact if_pos h_short
  · intro h_long
    simp [implementation]
    rw [if_neg]
    · simp
    · push_neg
      exact h_long

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · exact implementation_spec_holds arr