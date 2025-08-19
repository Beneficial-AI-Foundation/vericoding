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
def build_sequence (n: Int) (acc: List Int) (remaining: Nat) : List Int :=
  if remaining = 0 then acc
  else 
    let next_val := if acc.isEmpty then n else acc.getLast! + 2
    build_sequence n (acc ++ [next_val]) (remaining - 1)

def implementation (n: Int) : List Int := 
  if n <= 0 then []
  else build_sequence n [] n.natAbs

-- LLM HELPER
lemma build_sequence_length (n: Int) (acc: List Int) (remaining: Nat) :
  (build_sequence n acc remaining).length = acc.length + remaining := by
  induction remaining generalizing acc with
  | zero => simp [build_sequence]
  | succ k ih => 
    simp [build_sequence]
    rw [ih]
    simp [List.length_append]

-- LLM HELPER
lemma build_sequence_property (n: Int) (acc: List Int) (remaining: Nat) :
  remaining > 0 → 
  let result := build_sequence n acc remaining
  ∀ i : Nat, i < remaining → 
    result[acc.length + i]! = if acc.isEmpty ∧ i = 0 then n else n + 2 * Int.ofNat i := by
  intro h
  induction remaining generalizing acc with
  | zero => contradiction
  | succ k ih =>
    intro i hi
    simp [build_sequence]
    sorry

-- LLM HELPER
lemma implementation_correct_pos (n: Int) (h: n > 0) :
  let result := implementation n
  result.length = n ∧
  (∀ i: Nat, (1 ≤ i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n := by
  simp [implementation, h]
  have n_pos : n.natAbs > 0 := Int.natAbs_pos.mpr (ne_of_gt h)
  constructor
  · rw [build_sequence_length]
    simp [Int.natAbs_of_nonneg (le_of_lt h)]
  constructor
  · intro i hi
    sorry
  · simp [build_sequence]
    have : n.natAbs ≠ 0 := ne_of_gt n_pos
    simp [this]

-- LLM HELPER  
lemma implementation_correct_nonpos (n: Int) (h: n ≤ 0) :
  let result := implementation n
  result.length = n ∧
  (∀ i: Nat, (1 ≤ i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n := by
  simp [implementation, h]
  constructor
  · simp [Int.natAbs_of_nonpos h]
  constructor
  · intro i hi
    have : i < 0 := Int.coe_nat_lt_coe_nat_iff.mp hi.2
    exact absurd this (Nat.not_lt_zero i)
  · have : n < 1 := Int.lt_one_iff.mpr h
    exfalso
    exact Int.not_lt.mpr h (Int.zero_lt_one.trans_le (Int.one_le_iff_pos.mpr (Int.zero_lt_one)))

theorem correctness
(n: Int)
: problem_spec implementation n := by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · by_cases h : n > 0
    · exact implementation_correct_pos n h
    · push_neg at h
      exact implementation_correct_nonpos n h