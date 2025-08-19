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
def buildSequence (start: Int) (len: Nat) : List Int :=
  match len with
  | 0 => []
  | Nat.succ n => start :: buildSequence (start + 2) n

-- LLM HELPER
lemma buildSequence_length (start: Int) (len: Nat) : (buildSequence start len).length = len :=
  by
    induction len with
    | zero => simp [buildSequence]
    | succ n ih => simp [buildSequence, ih]

-- LLM HELPER
lemma buildSequence_first (start: Int) (len: Nat) (h: len > 0) : (buildSequence start len)[0]! = start :=
  by
    cases len with
    | zero => contradiction
    | succ n => simp [buildSequence]

-- LLM HELPER
lemma buildSequence_property (start: Int) (len: Nat) (i: Nat) (h1: 1 <= i) (h2: i < len) : 
  (buildSequence start len)[i]! = (buildSequence start len)[i-1]! + 2 :=
  by
    induction len generalizing i with
    | zero => 
      simp at h2
    | succ n ih =>
      simp [buildSequence]
      cases i with
      | zero => 
        simp at h1
      | succ j =>
        simp [List.get!]
        cases j with
        | zero =>
          simp [buildSequence]
        | succ k =>
          have h3: 1 <= k + 1 := by simp
          have h4: k + 1 < n := by
            simp at h2
            exact Nat.lt_of_succ_lt_succ h2
          exact ih (k + 1) h3 h4

def implementation (n: Int) : List Int := 
  if n <= 0 then [] else buildSequence n (Int.natAbs n)

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
      · simp [Int.natAbs_of_nonpos h]
      · constructor
        · intros i h1 h2
          simp at h2
        · simp [Int.natAbs_of_nonpos h]
    · simp
      constructor
      · exact buildSequence_length n (Int.natAbs n)
      · constructor
        · intros i h1 h2
          rw [← buildSequence_length n (Int.natAbs n)] at h2
          exact buildSequence_property n (Int.natAbs n) i h1 h2
        · have h_pos: (Int.natAbs n) > 0 := by
            simp [Int.natAbs_pos]
            push_neg at h
            exact Ne.symm h
          exact buildSequence_first n (Int.natAbs n) h_pos