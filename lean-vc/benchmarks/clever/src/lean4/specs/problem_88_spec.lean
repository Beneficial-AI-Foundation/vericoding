import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(lst: List Nat) :=
-- spec
let spec (result : List Nat) :=
  lst.length > 0 →
  result.length = lst.length ∧
  (∀ i, i < result.length →
    result[i]! ∈ lst ∧
    lst[i]! ∈ result ∧
    result.count (lst[i]!) = lst.count (lst[i]!)) ∧
  (lst.head! + lst.getLast!) ≡ 1 [MOD 2] →
    result.Sorted Nat.le ∧
  (lst.head! + lst.getLast!) ≡ 0 [MOD 2] →
    result.Sorted (fun a b => a ≥ b)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

def implementation (lst: List Nat) : List Nat := sorry

theorem correctness
(lst: List Nat)
: problem_spec implementation lst
:= sorry
