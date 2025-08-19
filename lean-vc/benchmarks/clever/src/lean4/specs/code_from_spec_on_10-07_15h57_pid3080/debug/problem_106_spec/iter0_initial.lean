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
def compute_element (i: Nat) : Int :=
  if Even i then Int.natCast (Nat.factorial i)
  else Int.natCast ((List.range (i+1)).sum)

def implementation (n: Int) : List Int := 
  if n ≤ 0 then []
  else (List.range (Int.natAbs n)).map (fun i => compute_element (i + 1))

-- LLM HELPER
lemma range_sum_formula (n: Nat) : (List.range (n+1)).sum = n * (n + 1) / 2 := by
  induction n with
  | zero => simp [List.range, List.sum_nil]
  | succ n ih =>
    rw [List.range_succ, List.sum_cons, ih]
    simp [Nat.add_mul, Nat.mul_add]
    ring

-- LLM HELPER
lemma length_correct (n: Int) (h: 0 ≤ n) : (implementation n).length = n := by
  simp [implementation, h]
  rw [List.length_map, List.length_range]
  exact Int.natAbs_of_nonneg h

-- LLM HELPER
lemma get_elem_correct (n: Int) (i: Nat) (h1: 1 ≤ i) (h2: i ≤ n) (h3: 0 ≤ n) :
  (implementation n)[i-1]! = compute_element i := by
  simp [implementation, h3]
  rw [List.getElem_map]
  simp [compute_element]
  congr 1
  omega

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  simp [problem_spec]
  by_cases h: n ≤ 0
  · use []
    simp [implementation, h]
    constructor
    · rfl
    · constructor
      · simp [List.length_nil]
        intro i h1 h2
        omega
      · simp [List.length_nil]
        intro i h1 h2
        omega
  · push_neg at h
    have h_nonneg: 0 ≤ n := by omega
    use implementation n
    constructor
    · rfl
    · constructor
      · exact length_correct n h_nonneg
      · constructor
        · intro i h1 h2 h_even
          rw [get_elem_correct n i h1 h2 h_nonneg]
          simp [compute_element, h_even]
        · intro i h1 h2 h_odd
          rw [get_elem_correct n i h1 h2 h_nonneg]
          simp [compute_element, h_odd]