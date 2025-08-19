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
def generate_sequence (n: Int) (acc: List Int) : List Int :=
  if acc.length >= n.natAbs then acc
  else 
    let next := if acc.isEmpty then n else acc.getLast! + 2
    generate_sequence n (acc ++ [next])

def implementation (n: Int) : List Int := 
  if n <= 0 then []
  else generate_sequence n []

-- LLM HELPER
lemma generate_sequence_length (n: Int) (acc: List Int) (h: n > 0) :
  (generate_sequence n acc).length = max acc.length n.natAbs := by
  sorry

-- LLM HELPER
lemma generate_sequence_first_elem (n: Int) (h: n > 0) :
  (generate_sequence n []).length > 0 → (generate_sequence n [])[0]! = n := by
  sorry

-- LLM HELPER
lemma generate_sequence_arithmetic (n: Int) (h: n > 0) :
  let result := generate_sequence n []
  ∀ i: Nat, (1 ≤ i ∧ i < result.length) → result[i]! = result[i-1]! + 2 := by
  sorry

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · simp [implementation]
    split_ifs with h
    · simp
      constructor
      · rfl
      constructor
      · intro i hi
        simp at hi
        exfalso
        exact Nat.not_lt_zero i hi.2
      · simp
    · have n_pos : n > 0 := by
        by_contra h_neg
        simp at h_neg
        exact h h_neg
      constructor
      · rw [generate_sequence_length n [] n_pos]
        simp [max_def]
        split_ifs
        · simp at *
          have : n > 0 := n_pos
          simp [Int.natAbs_pos] at this
          exact this
        · rfl
      constructor
      · exact generate_sequence_arithmetic n n_pos
      · exact generate_sequence_first_elem n n_pos