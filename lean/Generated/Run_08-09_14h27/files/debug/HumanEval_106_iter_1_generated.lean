import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def sum_range (n : Nat) : Nat := (List.range (n + 1)).sum

-- LLM HELPER
def compute_element (i : Nat) : Int :=
  if Even i then Int.ofNat (Nat.factorial i)
  else Int.ofNat (sum_range i)

def implementation (n: Int) : List Int :=
  if n ≤ 0 then []
  else (List.range n.natAbs).map (fun i => compute_element (i + 1))

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
lemma sum_range_eq (n : Nat) : sum_range n = (List.range (n + 1)).sum := rfl

-- LLM HELPER
lemma length_implementation (n : Int) (hn : 0 < n) : 
  (implementation n).length = n := by
  simp [implementation, hn]
  rw [List.length_map, List.length_range]
  simp [Int.natAbs_of_nonneg (le_of_lt hn)]

-- LLM HELPER
lemma get_implementation (n : Int) (i : Nat) (hn : 0 < n) (hi : i < n) :
  (implementation n)[i]! = compute_element (i + 1) := by
  simp [implementation, hn]
  rw [List.getElem_map]
  simp [List.getElem_range]
  omega

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec
  by_cases h : n ≤ 0
  · use []
    constructor
    · simp [implementation, h]
    · constructor
      · simp [implementation, h]
      · constructor
        · intro i hi
          simp at hi
          omega
        · intro i hi
          simp at hi
          omega
  · push_neg at h
    use implementation n
    constructor
    · rfl
    · constructor
      · exact length_implementation n h
      · constructor
        · intro i hi
          have hi_pos : 0 < i := hi.1
          have hi_bound : i < n := by omega
          have hi_cast : (i : Int) < n := by omega
          rw [get_implementation n (i-1) h]
          · simp [compute_element]
            split_ifs with heven
            · simp
            · simp
              exfalso
              exact heven hi.2.2
          · omega
        · intro i hi
          have hi_pos : 0 < i := hi.1
          have hi_bound : i < n := by omega
          rw [get_implementation n (i-1) h]
          · simp [compute_element]
            split_ifs with heven
            · exfalso
              rw [Nat.odd_iff_not_even] at hi
              exact hi.2.2 heven
            · simp [sum_range_eq]
          · omega