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

def implementation (lst1: List String) (lst2: List String) : List String := 
  let sum_chars (xs: List String) : Int :=
    xs.foldl (λ acc a => acc + a.length) 0
  if sum_chars lst1 ≤ sum_chars lst2 then lst1 else lst2

theorem correctness
(lst1: List String) (lst2: List String)
: problem_spec implementation lst1 lst2 := by
  simp [problem_spec, implementation]
  let sum_chars (xs: List String) : Int := xs.foldl (λ acc a => acc + a.length) 0
  use if sum_chars lst1 ≤ sum_chars lst2 then lst1 else lst2
  simp
  split_ifs with h
  · -- Case: sum_chars lst1 ≤ sum_chars lst2, so we return lst1
    simp [h]
    constructor
    · left
      rfl
    · constructor
      · le_refl _
      · constructor
        · exact h
        · intro h_eq
          rfl
  · -- Case: sum_chars lst1 > sum_chars lst2, so we return lst2
    simp [h]
    constructor
    · right
      rfl
    · constructor
      · simp at h
        omega
      · constructor
        · le_refl _
        · intro h_eq
          simp at h
          have : sum_chars lst1 ≤ sum_chars lst2 := by
            rw [h_eq]
          omega