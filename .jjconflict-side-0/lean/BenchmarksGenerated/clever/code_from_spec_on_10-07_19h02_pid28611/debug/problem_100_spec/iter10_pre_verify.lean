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
      simp [Int.ofNat_eq_coe]
      rw [h]
      simp
    · simp [Int.natAbs]
      have : Int.negSucc n < 0 := Int.negSucc_lt_zero n
      exfalso
      linarith
  · simp [List.length_map, List.length_range]
    cases' n with n n
    · simp [Int.natAbs]
      push_neg at h
      simp at h
      have : n > 0 := by omega
      simp [List.length_range]
      norm_cast
    · simp [Int.natAbs] at h ⊢
      exfalso
      exact h (Int.negSucc_lt_zero n)

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
      exact Int.coe_nat_lt_coe_nat_iff.2 (Int.coe_nat_lt_coe_nat_iff.1 h2)
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

-- LLM HELPER
lemma build_sequence_nonempty_iff (n: Int) : (buildSequence n).length > 0 ↔ n > 0 := by
  constructor
  · intro h
    by_contra h_neg
    push_neg at h_neg
    rw [buildSequence_empty_when_nonpos n h_neg] at h
    simp at h
  · intro h
    rw [buildSequence_length n]
    exact h

-- LLM HELPER
lemma spec_holds_for_empty_list (n: Int) (h: n ≤ 0) : 
  let result := buildSequence n
  result.length = n ∧
  (forall i: Nat, (1 <= i ∧ i < n) → (result[i]! = result[i-1]! + 2)) ∧
  result[0]! = n := by
  have n_eq_zero : n = 0 := int_le_zero_eq_zero n h (buildSequence_length n)
  rw [n_eq_zero]
  simp [buildSequence_empty_when_nonpos 0 (by omega : (0 : Int) ≤ 0)]
  intro i h_bounds
  exfalso
  omega

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec implementation
  use buildSequence n
  constructor
  · rfl
  · by_cases h: n > 0
    · constructor
      · exact buildSequence_length n
      · constructor
        · intros i h_bounds
          exact buildSequence_recurrence n i h_bounds.1 h_bounds.2
        · exact buildSequence_first n h
    · have : n ≤ 0 := by omega
      exact spec_holds_for_empty_list n this