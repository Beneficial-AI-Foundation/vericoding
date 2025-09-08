import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def abs_diff (a b : Rat) : Rat :=
  if a ≥ b then a - b else b - a

def implementation (scores guesses: List Rat) : List Rat :=
  List.zipWith abs_diff scores guesses

def problem_spec
-- function signature
(impl: List Rat → List Rat → List Rat)
-- inputs
(scores guesses: List Rat) :=
-- spec
let spec (result: List Rat) :=
  result.length = scores.length ∧
  scores.length = guesses.length ∧
  ∀ i, i < scores.length →
  if scores[i]! > guesses[i]! then result[i]! + guesses[i]! = scores[i]!
  else result[i]! + scores[i]! = guesses[i]!
-- program terminates
∃ result, impl scores guesses = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma abs_diff_property (a b : Rat) : 
  if a > b then abs_diff a b + b = a
  else abs_diff a b + a = b := by
  unfold abs_diff
  by_cases h : a ≥ b
  · by_cases h' : a > b
    · simp [h', h]
      ring
    · simp [h']
      have : a = b := by
        have h_le : a ≤ b := le_of_not_gt h'
        exact le_antisymm h_le h
      rw [this]
      simp [le_refl]
      ring
  · have : a < b := lt_of_not_ge h
    simp [not_le.mpr this]
    ring

-- LLM HELPER
lemma zipWith_length (f : Rat → Rat → Rat) (l1 l2 : List Rat) :
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  induction l1 generalizing l2 with
  | nil => simp [List.zipWith]
  | cons h t ih =>
    cases l2 with
    | nil => simp [List.zipWith]
    | cons h2 t2 => 
      simp [List.zipWith, ih]

-- LLM HELPER
lemma zipWith_get (f : Rat → Rat → Rat) (l1 l2 : List Rat) (i : Nat) 
  (h1 : i < l1.length) (h2 : i < l2.length) :
  (List.zipWith f l1 l2)[i]! = f l1[i]! l2[i]! := by
  induction l1 generalizing l2 i with
  | nil => simp at h1
  | cons h t ih =>
    cases l2 with
    | nil => simp at h2
    | cons h2 t2 =>
      cases i with
      | zero => simp [List.zipWith]
      | succ j =>
        simp [List.zipWith] at ih ⊢
        simp at h1 h2
        exact ih t2 j h1 h2

theorem correctness
(scores guesses: List Rat)
(h_same_length : scores.length = guesses.length)
: problem_spec implementation scores guesses := by
  unfold problem_spec implementation
  use List.zipWith abs_diff scores guesses
  constructor
  · rfl
  · simp only []
    constructor
    · rw [zipWith_length]
      simp [h_same_length]
    · constructor
      · exact h_same_length
      · intro i hi
        have h_guess : i < guesses.length := by
          rw [←h_same_length]
          exact hi
        rw [zipWith_get abs_diff scores guesses i hi h_guess]
        exact abs_diff_property scores[i]! guesses[i]!