import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Nat → Int)
(arr: List Int)
(k: Nat) :=
let spec (result: Int) :=
  1 ≤ arr.length → arr.length ≤ 100 → 1 ≤ k → k ≤ arr.length →
  ((∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → result = 0) ∧
  ∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else implementation arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)
∃ result, implementation arr k = result ∧
spec result

def implementation (arr: List Int) (k: Nat) : Int := sorry

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := sorry 