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
  if n <= 0 then []
  else List.range n.natAbs |>.map (fun i => n + 2 * i)

def implementation (n: Int) : List Int := buildSequence n

-- LLM HELPER
lemma buildSequence_length (n: Int) : (buildSequence n).length = n := by
  unfold buildSequence
  split_ifs with h
  · simp
    cases' n with n n
    · simp at h
      rfl
    · simp [Int.natAbs]
      have : Int.negSucc n ≤ 0 := by simp
      rfl
  · simp [List.length_map, List.length_range]
    cases' n with n n
    · simp [Int.natAbs]
      push_neg at h
      simp at h
      rfl
    · simp [Int.natAbs] at h ⊢
      exfalso
      exact h (Int.negSucc_neg_pos n)

-- LLM HELPER
lemma buildSequence_first (n: Int) (h: n > 0) : (buildSequence n)[0]! = n := by
  unfold buildSequence
  simp [h]
  cases' n with n n
  · simp [Int.natAbs]
    have : n > 0 := by omega
    simp [List.getElem_map, List.getElem_range]
    ring
  · simp at h

-- LLM HELPER
lemma buildSequence_recurrence (n: Int) (i: Nat) (h1: 1 <= i) (h2: i < n) : 
  (buildSequence n)[i]! = (buildSequence n)[i-1]! + 2 := by
  unfold buildSequence
  have n_pos : n > 0 := by omega
  simp [n_pos]
  have i_lt_natAbs : i < n.natAbs := by
    cases' n with n n
    · simp [Int.natAbs] at h2 ⊢
      exact h2
    · simp at h2
  have i_minus_1_lt_natAbs : i - 1 < n.natAbs := by
    omega
  simp [List.getElem_map, List.getElem_range, i_lt_natAbs, i_minus_1_lt_natAbs]
  ring

-- LLM HELPER
lemma buildSequence_empty_when_nonpos (n: Int) (h: n ≤ 0) : buildSequence n = [] := by
  unfold buildSequence
  simp [h]

-- LLM HELPER
lemma int_le_zero_eq_zero (n: Int) (h: n ≤ 0) (h_len: (buildSequence n).length = n) : n = 0 := by
  rw [buildSequence_empty_when_nonpos n h] at h_len
  simp at h_len
  exact h_len.symm

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
      · intros i h_bounds
        exact buildSequence_recurrence n i h_bounds.1 h_bounds.2
      · by_cases h: n > 0
        · exact buildSequence_first n h
        · have : n ≤ 0 := by omega
          have n_eq_zero : n = 0 := int_le_zero_eq_zero n this (buildSequence_length n)
          rw [buildSequence_empty_when_nonpos n (by omega : n ≤ 0)]
          simp
          exact n_eq_zero.symm