import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List String → List String → List String)
(lst1: List String) (lst2: List String) :=
let sum_chars (xs: List String) : Int :=
  xs.foldl (λ acc a => acc + a.length) 0;
let spec (result : List String) :=
  ((result = lst1) ∨ (result = lst2))
  ∧
  (sum_chars result ≤ sum_chars lst1)
  ∧
  (sum_chars result ≤ sum_chars lst2)
  ∧
  ((sum_chars lst1 = sum_chars lst2) → (result = lst1));
∃ result, implementation lst1 lst2 = result ∧
spec result

def implementation (lst1: List String) (lst2: List String) : List String := sorry

theorem correctness
(lst1: List String) (lst2: List String)
: problem_spec implementation lst1 lst2 := sorry 