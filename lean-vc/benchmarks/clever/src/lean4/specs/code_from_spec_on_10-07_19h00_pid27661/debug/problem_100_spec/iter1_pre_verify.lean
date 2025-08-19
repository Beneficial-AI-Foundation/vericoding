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
def generate_sequence (n: Int) : List Int :=
  if n <= 0 then []
  else List.range n.natAbs |>.map (fun i => n + 2 * i)

def implementation (n: Int) : List Int := generate_sequence n

-- LLM HELPER
lemma generate_sequence_length (n: Int) : (generate_sequence n).length = n := by
  unfold generate_sequence
  split_ifs with h
  · simp
    omega
  · simp [List.length_map, List.length_range]
    exact Int.natAbs_of_nonneg (Int.not_le.mp h)

-- LLM HELPER
lemma generate_sequence_first (n: Int) (h: n > 0) : (generate_sequence n)[0]! = n := by
  unfold generate_sequence
  simp [h]
  rw [List.getElem!_map, List.getElem!_range]
  simp
  omega

-- LLM HELPER
lemma generate_sequence_recurrence (n: Int) (i: Nat) (h1: 1 <= i) (h2: i < n) : 
  (generate_sequence n)[i]! = (generate_sequence n)[i-1]! + 2 := by
  unfold generate_sequence
  have n_pos : n > 0 := by omega
  simp [n_pos]
  rw [List.getElem!_map, List.getElem!_map, List.getElem!_range, List.getElem!_range]
  simp
  ring

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use generate_sequence n
  constructor
  · rfl
  · constructor
    · exact generate_sequence_length n
    · constructor
      · intros i h
        exact generate_sequence_recurrence n i h.1 h.2
      · by_cases h : n > 0
        · exact generate_sequence_first n h
        · unfold generate_sequence
          simp [h]
          have : n <= 0 := Int.not_lt.mp h
          have : n = 0 := by omega
          simp [this]