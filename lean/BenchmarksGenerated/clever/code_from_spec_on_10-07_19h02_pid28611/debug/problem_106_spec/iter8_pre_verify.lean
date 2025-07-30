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
  (result.length = n) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Even i) → (result[i-1]! = Nat.factorial i)) ∧
  (forall i: Nat, (1 ≤ i ∧ i ≤ n ∧ Odd i) → (result[i-1]! = (List.range (i+1)).sum))
-- program termination
∃ result, implementation n = result ∧
spec result

-- LLM HELPER
def triangular_number (k: Nat) : Nat := (List.range (k+1)).sum

-- LLM HELPER
def compute_element (i: Nat) : Int :=
  if Even i then Int.ofNat (Nat.factorial i)
  else Int.ofNat (triangular_number i)

def implementation (n: Int) : List Int := 
  if n ≤ 0 then []
  else (List.range n.natAbs).map (fun i => compute_element (i + 1))

-- LLM HELPER
lemma length_correct (n: Int) (h: n > 0) : 
  (implementation n).length = n := by
  simp [implementation]
  split
  · have : n ≤ 0 := by assumption
    linarith
  · simp [List.length_map, List.length_range]
    rw [Int.natAbs_of_nonneg (le_of_lt h)]
    simp

-- LLM HELPER
lemma even_case_correct (n: Int) (i: Nat) (h1: 1 ≤ i) (h2: ↑i ≤ n) (h3: Even i) :
  (implementation n)[i-1]! = Nat.factorial i := by
  have h_pos : n > 0 := by
    have : (1 : Int) ≤ n := by exact Int.coe_nat_le_coe_nat_iff.mpr h1
    have : (i : Int) ≤ n := h2
    linarith
  simp [implementation]
  split
  · have : n ≤ 0 := by assumption
    linarith
  · simp [List.getElem_map, List.getElem_range]
    simp [compute_element, h3]
    have h_in_range : i - 1 < n.natAbs := by
      have : i ≤ n.natAbs := by
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        exact Int.natCast_le.mp h2
      have : i - 1 < i := Nat.sub_lt (by linarith) (by norm_num)
      omega
    simp [h_in_range]
    rw [Nat.sub_add_cancel (le_of_lt (by linarith : 0 < i))]

-- LLM HELPER
lemma odd_case_correct (n: Int) (i: Nat) (h1: 1 ≤ i) (h2: ↑i ≤ n) (h3: Odd i) :
  (implementation n)[i-1]! = (List.range (i+1)).sum := by
  have h_pos : n > 0 := by
    have : (1 : Int) ≤ n := by exact Int.coe_nat_le_coe_nat_iff.mpr h1
    have : (i : Int) ≤ n := h2
    linarith
  simp [implementation]
  split
  · have : n ≤ 0 := by assumption
    linarith
  · simp [List.getElem_map, List.getElem_range]
    simp [compute_element, h3]
    simp [triangular_number]
    have h_in_range : i - 1 < n.natAbs := by
      have : i ≤ n.natAbs := by
        rw [Int.natAbs_of_nonneg (le_of_lt h_pos)]
        exact Int.natCast_le.mp h2
      have : i - 1 < i := Nat.sub_lt (by linarith) (by norm_num)
      omega
    simp [h_in_range]
    rw [Nat.sub_add_cancel (le_of_lt (by linarith : 0 < i))]

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec]
  use implementation n
  constructor
  · rfl
  · constructor
    · cases' Int.lt_or_ge n 1 with h h
      · simp [implementation]
        split
        · simp
        · simp
          have : n ≤ 0 := by linarith
          have : n.natAbs = 0 := by
            rw [Int.natAbs_eq_zero]
            linarith
          simp [this]
      · exact length_correct n h
    · constructor
      · intro i ⟨h1, h2, h3⟩
        exact even_case_correct n i h1 h2 h3
      · intro i ⟨h1, h2, h3⟩
        exact odd_case_correct n i h1 h2 h3