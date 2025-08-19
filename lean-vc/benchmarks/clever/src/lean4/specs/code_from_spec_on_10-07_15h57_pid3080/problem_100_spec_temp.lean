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
def build_sequence (start: Int) (len: Nat) : List Int :=
  match len with
  | 0 => []
  | Nat.succ k => start :: build_sequence (start + 2) k

def implementation (n: Int) : List Int := 
  if n <= 0 then [] else build_sequence n n.natAbs

-- LLM HELPER
lemma build_sequence_length (start: Int) (len: Nat) : 
  (build_sequence start len).length = len := by
  induction len with
  | zero => simp [build_sequence]
  | succ k ih => simp [build_sequence, ih]

-- LLM HELPER
lemma build_sequence_first (start: Int) (len: Nat) (h: len > 0) : 
  (build_sequence start len)[0]! = start := by
  cases len with
  | zero => contradiction
  | succ k => simp [build_sequence]

-- LLM HELPER
lemma build_sequence_step (start: Int) (len: Nat) (i: Nat) 
  (h1: 1 <= i) (h2: i < len) : 
  (build_sequence start len)[i]! = (build_sequence start len)[i-1]! + 2 := by
  induction len generalizing start i with
  | zero => 
    simp at h2
  | succ k ih =>
    simp [build_sequence]
    cases i with
    | zero => 
      simp at h1
    | succ j =>
      simp [List.get!]
      cases j with
      | zero =>
        simp [List.get!]
      | succ m =>
        have h3: 1 <= Nat.succ m := by simp
        have h4: Nat.succ m < k := by
          simp at h2
          exact Nat.lt_of_succ_lt_succ h2
        have := ih (start + 2) (Nat.succ m) h3 h4
        simp [List.get!] at this
        exact this

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
      · constructor
        · intro i h1 h2
          simp at h2
        · simp
    · simp
      constructor
      · exact build_sequence_length n n.natAbs
      · constructor
        · intro i h1 h2
          rw [← build_sequence_length n n.natAbs] at h2
          exact build_sequence_step n n.natAbs i h1 h2
        · have h_pos: n > 0 := by
            by_contra h_neg
            simp at h_neg
            exact h h_neg
          have h_natabs_pos: n.natAbs > 0 := by
            simp [Int.natAbs_pos]
            exact Ne.symm (ne_of_gt h_pos)
          exact build_sequence_first n n.natAbs h_natabs_pos