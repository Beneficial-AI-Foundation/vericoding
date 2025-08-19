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
lemma build_sequence_first (start: Int) (len: Nat) (h: len > 0) : 
  (build_sequence start len)[0]! = start := by
  cases len with
  | zero => contradiction
  | succ n => simp [build_sequence]

-- LLM HELPER
lemma build_sequence_step (start: Int) (len: Nat) (i: Nat) 
  (h1: 1 <= i) (h2: i < len) : 
  (build_sequence start len)[i]! = (build_sequence start len)[i-1]! + 2 := by
  induction len generalizing start i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => omega
    | succ j =>
      simp [build_sequence]
      cases j with
      | zero => simp [build_sequence]
      | succ k =>
        have h3: 1 <= k + 1 := by omega
        have h4: k + 1 < n + 1 := by omega
        rw [List.getElem_cons_succ, List.getElem_cons_succ]
        apply ih <;> omega

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  simp only [exists_prop]
  if h: n <= 0 then
    simp [h]
    use []
    simp
    constructor
    · rfl
    · simp
      constructor
      · omega
      · intro i h1 h2
        omega
  else
    simp [h]
    use build_sequence n n.natAbs
    constructor
    · rfl
    · simp
      constructor
      · exact build_sequence_length n n.natAbs
      · constructor
        · intro i h1 h2
          apply build_sequence_step
          · exact h1
          · rw [Int.natAbs_of_nonneg] at h2
            exact h2
            omega
        · apply build_sequence_first
          rw [Int.natAbs_pos]
          omega