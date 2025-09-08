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
  ((∀ i < k, arr[i]?.getD 0 ≤ 99 → arr[i]?.getD 0 < -99) → result = 0) ∨
  (∃ valid_elements : List Int, 
   (∀ x ∈ valid_elements, ∃ i < k, arr[i]?.getD 0 = x ∧ x ≤ 99 ∧ -99 ≤ x) ∧
   result = valid_elements.sum)
-- program termination
∃ result, impl arr k = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma filter_conjunction_to_and (arr : List Int) (k : Nat) :
  List.filter (fun x => decide (x ≤ 99 ∧ -99 ≤ x)) (List.take k arr) =
  List.filter (fun x => decide (x ≤ 99) && decide (-99 ≤ x)) (List.take k arr) := by
  rw [List.filter_congr]
  intro x _
  simp [decide_and]

-- LLM HELPER
lemma implementation_correct_case1 (arr: List Int) (k: Nat) :
  (∀ i < k, arr[i]?.getD 0 ≤ 99 → arr[i]?.getD 0 < -99) → 
  implementation arr k = 0 := by
  intro h
  simp [implementation, sum_filtered_elements, has_at_most_two_digits]
  have : (arr.take k).filter (fun x => x ≤ 99 ∧ -99 ≤ x) = [] := by
    simp [List.eq_nil_iff_forall_not_mem]
    intro x hx
    simp at hx
    obtain ⟨hx_mem, hx_le, hx_ge⟩ := hx
    have hx_in := List.mem_take.mp hx_mem
    obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hx_in.1
    have hi_bound : i < k := by
      rw [List.length_take] at hi_lt
      exact Nat.lt_min_iff.mp hi_lt |>.1
    rw [← hi_eq, List.get_take] at hx_le hx_ge
    simp at hi_eq
    have : arr[i]?.getD 0 = arr[i]! := by simp [List.getD_eq_get!, hi_lt]
    rw [← this] at hx_le hx_ge
    have : arr[i]?.getD 0 < -99 := h i hi_bound hx_le
    omega
  rw [this, List.sum_nil]

theorem correctness
(arr: List Int)
(k: Nat)
: problem_spec implementation arr k := by
  simp [problem_spec]
  use implementation arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4
    by_cases h_case : ∀ i < k, arr[i]?.getD 0 ≤ 99 → arr[i]?.getD 0 < -99
    · left
      exact implementation_correct_case1 arr k h_case
    · right
      push_neg at h_case
      use (arr.take k).filter (fun x => x ≤ 99 ∧ -99 ≤ x)
      constructor
      · intro x hx
        simp at hx
        obtain ⟨hx_mem, hx_prop⟩ := hx
        have hx_in := List.mem_take.mp hx_mem
        obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp hx_in.1
        have hi_bound : i < k := by
          rw [List.length_take] at hi_lt
          exact Nat.lt_min_iff.mp hi_lt |>.1
        use i, hi_bound
        have : arr[i]?.getD 0 = arr[i]! := by simp [List.getD_eq_get!, hi_lt]
        rw [← hi_eq, List.get_take, ← this]
        exact ⟨rfl, hx_prop⟩
      · simp [implementation, sum_filtered_elements, has_at_most_two_digits]

-- #test implementation ([111, 21, 3, 4000, 5, 6, 7, 8, 9]: List Int) 4 = 24