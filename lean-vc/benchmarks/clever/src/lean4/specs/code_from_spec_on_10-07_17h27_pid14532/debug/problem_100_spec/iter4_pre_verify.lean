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
def generate_sequence (n: Int) (k: Nat) : List Int :=
  match k with
  | 0 => []
  | 1 => [n]
  | k' + 1 => n :: generate_sequence (n + 2) k'

def implementation (n: Int) : List Int := 
  if n <= 0 then []
  else generate_sequence n n.natAbs

-- LLM HELPER
lemma generate_sequence_length (start: Int) (k: Nat) : 
  (generate_sequence start k).length = k := by
  induction k using Nat.strong_induction with
  | h k ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      cases k' with
      | zero => rfl
      | succ k'' => 
        rw [generate_sequence]
        rw [List.length_cons]
        rw [ih (k' + 1)]
        simp
        omega

-- LLM HELPER  
lemma generate_sequence_first (start: Int) (k: Nat) (h: k > 0) :
  (generate_sequence start k)[0]! = start := by
  cases k with
  | zero => contradiction
  | succ k' =>
    cases k' with
    | zero => rfl
    | succ k'' => 
      simp [generate_sequence]

-- LLM HELPER
lemma generate_sequence_arithmetic (start: Int) (k: Nat) (i: Nat) 
  (h1: 1 <= i) (h2: i < k) :
  (generate_sequence start k)[i]! = (generate_sequence start k)[i-1]! + 2 := by
  induction k, i using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => omega
      | succ k'' =>
        rw [generate_sequence]
        cases i with
        | zero => omega
        | succ i' =>
          cases i' with
          | zero => 
            rw [List.getElem_cons_one, List.getElem_cons_zero]
            rw [generate_sequence]
            cases k'' with
            | zero => rfl
            | succ k''' => rfl
          | succ i'' =>
            rw [List.getElem_cons_succ, List.getElem_cons_succ]
            apply ih (k' + 1) (by omega) (i' + 1) (by omega) (by omega)

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  rw [problem_spec, implementation]
  if h : n <= 0 then
    rw [if_pos h]
    use []
    constructor
    · rfl
    · constructor
      · simp [List.length_nil]
        omega
      · constructor
        · intro i h1
          omega
        · simp

  else
    rw [if_neg h]
    use generate_sequence n n.natAbs
    constructor
    · rfl
    · constructor
      · rw [generate_sequence_length]
        simp [Int.natAbs_of_nonneg]
        omega
      · constructor
        · intro i h1
          apply generate_sequence_arithmetic
          exact h1.1
          have : n > 0 := by omega
          rw [Int.natAbs_of_nonneg (by omega)] at h1
          exact h1.2
        · apply generate_sequence_first
          simp [Int.natAbs_of_nonneg]
          omega