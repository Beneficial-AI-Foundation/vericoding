import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(arr: List Int) :=
-- spec
let spec (result : Int) :=
  let swaps_done (arr1: List Int) (arr2: List Int) :=
    ((List.finRange (arr1.length)).filter (fun idx => arr1[idx]? ≠ arr2[idx]?)).length/2
  ∀ palin_perm, (List.Perm arr palin_perm) ∧ (List.Palindrome palin_perm) →
    result ≤ (swaps_done arr palin_perm)
-- program termination
∃ result, implementation arr = result ∧
spec result

def implementation (arr: List Int) : Int := sorry

theorem correctness
(arr: List Int)
: problem_spec implementation arr
:= sorry
