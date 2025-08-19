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
  if k = 0 then []
  else if k = 1 then [n]
  else n :: generate_sequence (n + 2) (k - 1)

def implementation (n: Int) : List Int := 
  if n <= 0 then []
  else generate_sequence n n.natAbs

-- LLM HELPER
lemma generate_sequence_length (start: Int) (k: Nat) : 
  (generate_sequence start k).length = k := by
  induction k with
  | zero => simp [generate_sequence]
  | succ k ih => 
    simp [generate_sequence]
    cases k with
    | zero => simp [generate_sequence]
    | succ k' => 
      simp [generate_sequence]
      exact ih

-- LLM HELPER  
lemma generate_sequence_first (start: Int) (k: Nat) (h: k > 0) :
  (generate_sequence start k)[0]! = start := by
  cases k with
  | zero => contradiction
  | succ k' =>
    cases k' with
    | zero => simp [generate_sequence]
    | succ k'' => simp [generate_sequence]

-- LLM HELPER
lemma generate_sequence_arithmetic (start: Int) (k: Nat) (i: Nat) 
  (h1: 1 <= i) (h2: i < k) :
  (generate_sequence start k)[i]! = (generate_sequence start k)[i-1]! + 2 := by
  sorry

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec, implementation]
  if h : n <= 0 then
    simp [h]
    use []
    simp
  else
    simp [h]
    use generate_sequence n n.natAbs
    constructor
    · rfl
    · constructor
      · simp [generate_sequence_length]
      · constructor
        · intro i h1 h2
          apply generate_sequence_arithmetic
          exact h1
          exact h2
        · apply generate_sequence_first
          omega