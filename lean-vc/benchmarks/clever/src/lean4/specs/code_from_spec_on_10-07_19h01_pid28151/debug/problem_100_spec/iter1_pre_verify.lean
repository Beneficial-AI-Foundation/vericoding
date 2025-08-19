import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: Int → List Int)
-- inputs
(n: Int) :=
-- spec
let spec (result: List Int) :=
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def buildSequence (n: Int) : List Int :=
  if n ≤ 0 then []
  else 
    let rec aux (count: Nat) (current: Int) (acc: List Int) : List Int :=
      if count = 0 then acc.reverse
      else aux (count - 1) (current + 2) (current :: acc)
    aux n.natAbs n []

def implementation (n: Int) : List Int := buildSequence n

-- LLM HELPER
lemma buildSequence_length (n: Int) : (buildSequence n).length = n := by
  unfold buildSequence
  split_ifs with h
  · simp [h]
  · have h' : n > 0 := by linarith
    have n_pos : 0 < n.natAbs := Int.natAbs_pos.mpr (ne_of_gt h')
    let rec aux_length (count: Nat) (current: Int) (acc: List Int) : 
      (buildSequence.aux count current acc).length = count + acc.length := by
      unfold buildSequence.aux
      split_ifs with h_count
      · simp [h_count]
      · have : count ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_count
        rw [aux_length (count - 1) (current + 2) (current :: acc)]
        simp [List.length_cons]
        omega
    have := aux_length n.natAbs n []
    simp at this
    exact this

-- LLM HELPER
lemma buildSequence_first_element (n: Int) (h: n > 0) : (buildSequence n)[0]! = n := by
  unfold buildSequence
  simp [h]
  let rec aux_first (count: Nat) (current: Int) (acc: List Int) (h_count: count > 0) : 
    ((buildSequence.aux count current acc).reverse)[0]! = current := by
    unfold buildSequence.aux
    split_ifs with h_zero
    · contradiction
    · sorry -- This would need more complex induction
  sorry

-- LLM HELPER
lemma buildSequence_arithmetic_progression (n: Int) (h: n > 0) : 
  ∀ i: Nat, (1 ≤ i ∧ i < n) → (buildSequence n)[i]! = (buildSequence n)[i-1]! + 2 := by
  sorry

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use buildSequence n
  constructor
  · rfl
  · constructor
    · exact buildSequence_length n
    · constructor
      · by_cases h : n > 0
        · exact buildSequence_arithmetic_progression n h
        · intro i hi
          have : (buildSequence n).length = n := buildSequence_length n
          have : n ≤ 0 := le_of_not_gt h
          have : i < n := hi.2
          have : i < 0 := by linarith [this, ‹n ≤ 0›]
          have : ¬(1 ≤ i) := by linarith [this]
          contradiction
      · by_cases h : n > 0
        · exact buildSequence_first_element n h
        · have : (buildSequence n).length = n := buildSequence_length n
          have : n ≤ 0 := le_of_not_gt h
          have : (buildSequence n).length ≤ 0 := by linarith [this, ‹(buildSequence n).length = n›]
          have : (buildSequence n).length = 0 := by linarith [List.length_nonneg, this]
          unfold buildSequence at this
          simp [le_of_not_gt h] at this
          have : buildSequence n = [] := List.length_eq_zero.mp this
          rw [this]
          simp [Int.natAbs_of_nonneg (le_of_not_gt h)]