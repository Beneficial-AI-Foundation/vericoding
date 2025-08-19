import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(impl: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
lst ≠ [] → ∀ i,  i < lst.length ∧ i % 2 = 0 →
  (lst.length = 1 → impl lst = 0) ∧
  (i + 1 < lst.length →
    (lst[i + 1]! % 2 = 1 →
    impl (lst.drop i) = lst[i + 1]! + (if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)) ∧
    (lst[i + 1]! % 2 = 0 →
    impl (lst.drop i) = if i + 2 < lst.length then impl (lst.drop (i+2)) else 0)
  )
-- program terminates
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

def implementation (lst: List Int) : Int := sorry

theorem correctness
(lst: List Int)
: problem_spec implementation lst := sorry
