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
def compute_value (i: Nat) : Int :=
  if Even i then (Nat.factorial i : Int)
  else ((List.range (i+1)).sum : Int)

def implementation (n: Int) : List Int := 
  if n ≤ 0 then []
  else (List.range (Int.natAbs n)).map (fun i => compute_value (i + 1))

-- LLM HELPER
lemma range_sum_formula (n: Nat) : (List.range (n + 1)).sum = n * (n + 1) / 2 := by
  induction n with
  | zero => 
    simp [List.range_zero, List.sum_nil]
  | succ n ih =>
    rw [List.sum_range_succ]
    rw [ih]
    ring

-- LLM HELPER
lemma length_helper (n: Int) (h: 0 < n) : 
  ((List.range (Int.natAbs n)).map (fun i => compute_value (i + 1))).length = n := by
  rw [List.length_map, List.length_range]
  rw [Int.natAbs_of_nonneg (le_of_lt h)]
  simp

-- LLM HELPER
lemma get_helper (n: Int) (h: 0 < n) (i: Nat) (hi: i < Int.natAbs n) :
  ((List.range (Int.natAbs n)).map (fun j => compute_value (j + 1)))[i]! = compute_value (i + 1) := by
  rw [List.getElem_map, List.getElem_range]

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec
  unfold implementation
  by_cases h: n ≤ 0
  · simp [h]
    use []
    simp
    constructor
    · cases' h with h h
      · simp [h]
      · simp [Int.natCast_eq_zero] at h
        exact h
    · constructor
      · intro i hi
        simp at hi
        omega
      · intro i hi
        simp at hi
        omega
  · push_neg at h
    simp [h]
    use (List.range (Int.natAbs n)).map (fun i => compute_value (i + 1))
    constructor
    · rfl
    · constructor
      · rw [List.length_map, List.length_range]
        rw [Int.natAbs_of_nonneg (le_of_lt h)]
      · constructor
        · intro i hi
          have hi_pos: 0 < Int.natAbs n := by
            rw [Int.natAbs_pos]
            exact ne_of_gt h
          have hi_bound: i - 1 < Int.natAbs n := by
            rw [Int.natAbs_of_nonneg (le_of_lt h)] at *
            omega
          rw [get_helper n h (i-1) hi_bound]
          unfold compute_value
          simp [hi.2.2]
        · intro i hi
          have hi_pos: 0 < Int.natAbs n := by
            rw [Int.natAbs_pos]
            exact ne_of_gt h
          have hi_bound: i - 1 < Int.natAbs n := by
            rw [Int.natAbs_of_nonneg (le_of_lt h)] at *
            omega
          rw [get_helper n h (i-1) hi_bound]
          unfold compute_value
          simp [hi.2.2]