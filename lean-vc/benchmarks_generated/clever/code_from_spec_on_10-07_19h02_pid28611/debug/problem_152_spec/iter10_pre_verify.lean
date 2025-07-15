import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
def compute_difference (s g : Rat) : Rat :=
  if s > g then s - g else g - s

def implementation (scores guesses: List Rat) : List Rat := 
  if scores.length = guesses.length then
    List.zipWith compute_difference scores guesses
  else
    []

-- LLM HELPER
lemma zipWith_length (f : Rat → Rat → Rat) (l1 l2 : List Rat) :
  (List.zipWith f l1 l2).length = min l1.length l2.length := by
  rw [List.length_zipWith]

-- LLM HELPER
lemma zipWith_get (f : Rat → Rat → Rat) (l1 l2 : List Rat) (i : Nat) 
  (h : i < min l1.length l2.length) :
  (List.zipWith f l1 l2)[i]! = f l1[i]! l2[i]! := by
  rw [List.getElem!_zipWith]
  exact h

-- LLM HELPER
lemma compute_difference_spec (s g : Rat) :
  if s > g then (compute_difference s g) + g = s
  else (compute_difference s g) + s = g := by
  unfold compute_difference
  split_ifs with h
  · simp [sub_add_cancel]
  · simp [sub_add_cancel]

theorem correctness
(scores guesses: List Rat)
: problem_spec implementation scores guesses := by
  unfold problem_spec implementation
  split_ifs with h
  · use List.zipWith compute_difference scores guesses
    constructor
    · rfl
    · constructor
      · rw [zipWith_length]
        simp [h]
      · constructor
        · exact h
        · intro i hi
          rw [zipWith_get]
          · exact compute_difference_spec scores[i]! guesses[i]!
          · rw [min_def]
            split_ifs with h2
            · exact hi
            · rw [h] at hi
              exact hi
  · use []
    constructor
    · rfl
    · constructor
      · simp
      · constructor
        · exact h
        · intro i hi
          simp at hi