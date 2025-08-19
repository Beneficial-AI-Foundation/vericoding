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
  | Nat.succ n => start :: build_sequence (start + 2) n

def implementation (n: Int) : List Int := 
  if n <= 0 then [] else build_sequence n n.natAbs

-- LLM HELPER
lemma build_sequence_length (start: Int) (len: Nat) : 
  (build_sequence start len).length = len := by
  induction len with
  | zero => simp [build_sequence]
  | succ n ih => simp [build_sequence, ih]

-- LLM HELPER
lemma build_sequence_get (start: Int) (len: Nat) (i: Nat) (h: i < len) :
  (build_sequence start len)[i]! = start + 2 * i := by
  revert start i h
  induction len with
  | zero => intro start i h; exact absurd h (Nat.not_lt_zero i)
  | succ n ih => 
    intro start i h
    cases' i with i'
    · simp [build_sequence, List.get!]
    · simp [build_sequence, List.get!, ih]
      ring

-- LLM HELPER
lemma build_sequence_consecutive (start: Int) (len: Nat) (i: Nat) 
  (h1: 1 <= i) (h2: i < len) :
  (build_sequence start len)[i]! = (build_sequence start len)[i-1]! + 2 := by
  have h_pred : i - 1 < len := by
    cases' i with i'
    · simp at h1
    · simp [Nat.succ_sub_succ_eq_sub, tsub_zero]
      exact Nat.lt_of_succ_lt h2
  rw [build_sequence_get start len i h2, build_sequence_get start len (i-1) h_pred]
  cases' i with i'
  · simp at h1
  · simp [Nat.succ_sub_succ_eq_sub, tsub_zero]
    ring

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  split_ifs with h
  · simp [build_sequence]
    constructor
    · rfl
    · constructor
      · intro i h1 h2
        simp at h2
      · simp [List.get!]
  · push_neg at h
    use build_sequence n n.natAbs
    constructor
    · rfl
    · constructor
      · rw [build_sequence_length]
        exact Int.natAbs_of_nonneg h
      · constructor
        · intro i h1 h2
          have h_len : i < n.natAbs := by
            rw [← Int.natAbs_of_nonneg h] at h2
            exact h2
          exact build_sequence_consecutive n n.natAbs i h1 h_len
        · rw [build_sequence_get n n.natAbs 0]
          · simp
          · rw [Int.natAbs_of_nonneg h]
            exact Int.natAbs_pos.mpr (Ne.symm (ne_of_lt h))