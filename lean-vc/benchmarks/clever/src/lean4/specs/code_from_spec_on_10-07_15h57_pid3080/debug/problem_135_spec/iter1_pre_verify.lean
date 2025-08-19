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
  if arr.length ≤ 1 then -1
  else 
    let last := arr.length - 1
    let i := if arr[last]! < arr[last - 1]! then Int.ofNat last else -1
    max (implementation (arr.take last)) i

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  unfold problem_spec
  exists implementation arr
  constructor
  · rfl
  · intro h_no_duplicates
    constructor
    · intro h_short
      simp [implementation]
      cases' h_short with h_empty h_single
      · simp [h_empty]
      · simp [h_single]
    · intro h_long
      simp [implementation]
      have h_pos : 1 < arr.length := h_long
      simp [h_pos]
      rfl