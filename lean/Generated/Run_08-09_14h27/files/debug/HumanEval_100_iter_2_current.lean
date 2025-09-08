/- 
function_signature: "def make_a_pile(n: int) -> List[int]"
docstring: |
    Given a positive integer n, you have to make a pile of n levels of stones.
    The first level has n stones.
    The number of stones in the next level is:
      - the next odd number if n is odd.
      - the next even number if n is even.
    Return the number of stones in each level in a list, where element at index
    i represents the number of stones in the level (i+1).
test_cases:
  - input: 3
    expected_output: [3, 5, 7]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def make_pile_aux (start: Int) (count: Int) : List Int :=
  if count <= 0 then []
  else start :: make_pile_aux (start + 2) (count - 1)
termination_by count.natAbs
decreasing_by
  simp_wf
  omega

def implementation (n: Int) : List Int :=
  if n <= 0 then [] else make_pile_aux n n

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
lemma make_pile_aux_length (start: Int) (count: Int) :
  (make_pile_aux start count).length = max count 0 := by
  induction' count using Int.negInduction with k hk k hk
  · simp [make_pile_aux]
  · simp [make_pile_aux]
    cases' Nat.succ_pos k with h
    have : (k : Int) + 1 > 0 := Int.coe_nat_pos.mpr (Nat.succ_pos k)
    simp [this, hk]
    omega

-- LLM HELPER
lemma make_pile_aux_get (start: Int) (count: Int) (i: Nat) (hi: i < (make_pile_aux start count).length) :
  (make_pile_aux start count)[i]! = start + 2 * i := by
  induction' count using Int.negInduction with k hk k hk generalizing start i
  · simp [make_pile_aux] at hi
  · simp [make_pile_aux] at hi
    have pos : (k : Int) + 1 > 0 := Int.coe_nat_pos.mpr (Nat.succ_pos k)
    simp [pos] at hi ⊢
    cases' i with i
    · simp
    · simp [List.get_cons_succ]
      have : i < (make_pile_aux (start + 2) k).length := by
        simp at hi
        exact Nat.lt_of_succ_lt_succ hi
      rw [hk (start + 2) i this]
      ring

-- LLM HELPER
lemma implementation_spec_pos (n: Int) (hn: 0 < n) :
  let result := implementation n
  result.length = n ∧
  (∀ i: Nat, (1 ≤ i ∧ i < n) → result[i]! = result[i-1]! + 2) ∧
  result[0]! = n := by
  simp [implementation]
  have : ¬n ≤ 0 := not_le.mpr hn
  simp [this]
  constructor
  · rw [make_pile_aux_length]
    simp [max_def, hn]
  constructor
  · intro i hi
    have h_len : (make_pile_aux n n).length = n := by
      rw [make_pile_aux_length]
      simp [max_def, hn]
    have hi_bound : i < (make_pile_aux n n).length := by
      rw [h_len]
      exact Int.natCast_lt.mp hi.2
    have hi_prev : i - 1 < (make_pile_aux n n).length := by
      rw [h_len]
      omega
    rw [make_pile_aux_get n n i hi_bound]
    rw [make_pile_aux_get n n (i-1) hi_prev]
    omega
  · have h_len : (make_pile_aux n n).length = n := by
      rw [make_pile_aux_length]
      simp [max_def, hn]
    have h_pos : 0 < (make_pile_aux n n).length := by
      rw [h_len]
      exact hn
    have h_bound : 0 < (make_pile_aux n n).length := h_pos
    rw [make_pile_aux_get n n 0 h_bound]
    simp

theorem correctness
(n: Int)
: problem_spec implementation n
:= by
  unfold problem_spec
  use implementation n
  constructor
  · rfl
  · by_cases hn: 0 < n
    · exact implementation_spec_pos n hn
    · simp [implementation]
      push_neg at hn
      have : n ≤ 0 := hn
      simp [this]
      omega

-- #test implementation 3 = [3, 5, 7]
-- #test implementation 4 = [4,6,8,10]
-- #test implementation 5 = [5, 7, 9, 11, 13]
-- #test implementation 6 = [6, 8, 10, 12, 14, 16]
-- #test implementation 8 = [8, 10, 12, 14, 16, 18, 20, 22]