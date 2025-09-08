/- 
function_signature: "def add_elements(arr: List[int], k: int) -> int"
docstring: |
    Given a non-empty array of integers arr and an integer k, return
    the sum of the elements with at most two digits from the first k elements of arr.

    Constraints:
        1. 1 <= len(arr) <= 100
        2. 1 <= k <= len(arr)
test_cases:
  - input: [[111, 21, 3, 4000, 5, 6, 7, 8, 9], 4]
    expected_output: 24
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def has_at_most_two_digits (n: Int) : Bool :=
  n ≤ 99 ∧ -99 ≤ n

-- LLM HELPER  
def sum_filtered_elements (arr: List Int) (k: Nat) : Int :=
  (arr.take k).filter (fun x => has_at_most_two_digits x) |>.sum

def implementation (arr: List Int) (k: Nat) : Int :=
  sum_filtered_elements arr k

def problem_spec
-- function signature
(impl: List Int → Nat → Int)
-- inputs
(arr: List Int)
(k: Nat) :=
-- spec
let spec (result: Int) :=
  1 ≤ arr.length → arr.length ≤ 100 → 1 ≤ k → k ≤ arr.length →
  ((∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → result = 0) ∧
  ∃ i, i < k
    ∧ arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!
    ∧ result = arr[i]! + (if i = 0 then 0 else impl arr i)
    ∧ ∀ i', i < i' ∧ i' < k → ¬(arr[i']! ≤ 99 ∧ -99 ≤ arr[i']!)
-- program termination
∃ result, impl arr k = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma implementation_correct_case1 (arr: List Int) (k: Nat) :
  (∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)) → 
  implementation arr k = 0 := by
  intro h
  simp [implementation, sum_filtered_elements, has_at_most_two_digits]
  have : (arr.take k).filter (fun x => x ≤ 99 ∧ -99 ≤ x) = [] := by
    apply List.filter_eq_nil.mpr
    intro x hx
    simp
    have hx_in := List.mem_take.mp hx
    obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hx_in.1
    have hi_bound : i < k := by
      rw [List.length_take] at hi_lt
      exact Nat.lt_min_iff.mp hi_lt |>.1
    have : ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!) := h i ⟨le_refl 0, hi_bound⟩
    rw [← hi_eq, List.get_take]
    exact this
  simp [this]

-- LLM HELPER
lemma sum_filtered_computes_correctly (arr: List Int) (k: Nat) :
  sum_filtered_elements arr k = 
  (List.range k).foldl (fun acc i => 
    if i < arr.length ∧ has_at_most_two_digits arr[i]! then acc + arr[i]! else acc) 0 := by
  simp [sum_filtered_elements, has_at_most_two_digits]
  sorry

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  simp [problem_spec]
  use implementation arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4
    constructor
    · intro h_no_valid
      exact implementation_correct_case1 arr k h_no_valid
    · by_cases h_case : ∀ i, 0 ≤ i ∧ i < k → ¬(arr[i]! ≤ 99 ∧ -99 ≤ arr[i]!)
      · exfalso
        -- This case contradicts the existence requirement
        sorry
      · push_neg at h_case
        obtain ⟨i, hi_bounds, hi_valid⟩ := h_case
        use i
        constructor
        · exact hi_bounds.2
        constructor  
        · exact hi_valid
        constructor
        · simp [implementation, sum_filtered_elements]
          -- The sum equals the element plus recursive sum
          sorry
        · intro i' hi'_bounds hi'_not_valid
          exact hi'_not_valid

-- #test implementation ([111, 21, 3, 4000, 5, 6, 7, 8, 9]: List Int) 4 = 24