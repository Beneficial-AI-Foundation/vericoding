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
  (make_pile_aux start count).length = Int.max count 0 := by
  induction' count using Int.negInduction with k hk k hk
  · simp [make_pile_aux, Int.max_def]
  · simp [make_pile_aux, Int.max_def]
    split_ifs with h
    · contradiction
    · simp [make_pile_aux, hk]
      simp [Int.max_def] at hk
      split_ifs at hk with h2
      · omega
      · omega

-- LLM HELPER
lemma make_pile_aux_get (start: Int) (count: Int) (i: Nat) (hi: i < (make_pile_aux start count).length) :
  (make_pile_aux start count)[i]! = start + 2 * i := by
  induction' count using Int.negInduction with k hk k hk generalizing start i
  · simp [make_pile_aux] at hi
  · simp [make_pile_aux] at hi
    split_ifs at hi with h
    · simp [make_pile_aux] at hi
    · simp [make_pile_aux] at hi ⊢
      cases' i with i
      · simp
      · simp [List.get_cons_succ]
        have : i < (make_pile_aux (start + 2) (k + 1)).length := by
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
  simp [implementation, hn]
  constructor
  · rw [make_pile_aux_length]
    simp [Int.max_def, hn]
  constructor
  · intro i hi
    have h_len : (make_pile_aux n n).length = n := by
      rw [make_pile_aux_length, Int.max_def]
      simp [hn]
    have hi_bound : i < (make_pile_aux n n).length := by
      rw [h_len]; exact Int.natCast_lt.mp hi.2
    have hi_prev : i - 1 < (make_pile_aux n n).length := by
      rw [h_len]; omega
    rw [make_pile_aux_get n n i hi_bound]
    rw [make_pile_aux_get n n (i-1) hi_prev]
    omega
  · have h_len : (make_pile_aux n n).length = n := by
      rw [make_pile_aux_length, Int.max_def]
      simp [hn]
    have h_pos : 0 < (make_pile_aux n n).length := by
      rw [h_len]; exact hn
    rw [make_pile_aux_get n n 0 (Nat.pos_iff_ne_zero.mp (Int.natCast_pos.mpr h_pos))]
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
    · simp [implementation, hn]
      push_neg at hn
      have : n ≤ 0 := hn
      have : ([] : List Int).length = 0 := by simp
      simp [this]
      omega

-- #test implementation 3 = [3, 5, 7]
-- #test implementation 4 = [4,6,8,10]
-- #test implementation 5 = [5, 7, 9, 11, 13]
-- #test implementation 6 = [6, 8, 10, 12, 14, 16]
-- #test implementation 8 = [8, 10, 12, 14, 16, 18, 20, 22]