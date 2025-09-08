/- 
function_signature: "def by_length(arr: List[int]) -> List[string]"
docstring: |
    Given an array of integers, sort the integers that are between 1 and 9 inclusive,
    reverse the resulting array, and then replace each digit by its corresponding name from
    "One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine".
test_cases:
  - input: [2, 1, 1, 4, 5, 8, 2, 3]
    expected_output: ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]
  - input: []
    expected_output: []
  - input: [1, -1 , 55]
    expected_output: ['One']
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def digit_to_name (n: Int) : String :=
  match n with
  | 1 => "One"
  | 2 => "Two" 
  | 3 => "Three"
  | 4 => "Four"
  | 5 => "Five"
  | 6 => "Six"
  | 7 => "Seven"
  | 8 => "Eight"
  | 9 => "Nine"
  | _ => ""

def implementation (arr: List Int) : List String :=
  let filtered := arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)
  let sorted := filtered.mergeSort (· ≤ ·)
  let reversed := sorted.reverse
  reversed.map digit_to_name

def problem_spec
-- function signature
(implementation: List Int → List String)
-- inputs
(arr: List Int) :=
-- spec
let spec (result: List String) :=
  let digits: List String := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"];
  (forall s: String, (s ∈ result → s ∈ digits)) ∧
  (arr.length ≥ result.length) ∧
  (forall x: Nat, ((x: Int) ∈ arr ∧ 1 ≤ x ∧ x ≤ 9) → (digits[x-1]! ∈ result)) ∧
  (List.Sorted Int.le (List.map (fun (s: String) => (List.idxOf s digits) + 1) result).reverse)
-- program termination
∃ result, implementation arr = result ∧
spec result

-- LLM HELPER
lemma digit_to_name_in_digits (x: Int) (h: 1 ≤ x ∧ x ≤ 9) :
  digit_to_name x ∈ ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"] := by
  cases' h with h1 h2
  interval_cases x <;> simp [digit_to_name]

-- LLM HELPER
lemma filter_length_le (arr: List Int) : 
  (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).length ≤ arr.length := by
  exact List.length_filter_le (fun x => 1 ≤ x ∧ x ≤ 9) arr

-- LLM HELPER
lemma name_to_digit_inverse (x: Int) (h: 1 ≤ x ∧ x ≤ 9) :
  let digits := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  digits[(x - 1).natAbs]! = digit_to_name x := by
  cases' h with h1 h2
  interval_cases x <;> simp [digit_to_name]

-- LLM HELPER
lemma digit_name_idxOf (x: Int) (h: 1 ≤ x ∧ x ≤ 9) :
  let digits := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  List.idxOf (digit_to_name x) digits = x.natAbs - 1 := by
  cases' h with h1 h2
  interval_cases x <;> simp [digit_to_name]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · simp [implementation]
    constructor
    · -- All strings in result are in digits
      intro s hs
      simp at hs
      obtain ⟨x, hx_in, hx_eq⟩ := hs
      rw [← hx_eq]
      have hx_bounds : x ∈ arr.filter (fun y => 1 ≤ y ∧ y ≤ 9) := by
        exact List.mem_of_mem_reverse hx_in
      simp [List.mem_filter] at hx_bounds
      obtain ⟨_, hx_filter⟩ := hx_bounds
      exact digit_to_name_in_digits x hx_filter
    constructor
    · -- Length constraint
      have h1 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).length ≤ arr.length := filter_length_le arr
      have h2 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).length := List.length_mergeSort _ _
      have h3 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.length := List.length_reverse _
      have h4 : ((arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.map digit_to_name).length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.length := List.length_map _ _
      rw [h4, h3, h2]
      exact h1
    constructor
    · -- All valid digits appear in result
      intro x hx
      cases' hx with hx_in hx_bounds
      have hx_filtered : ↑x ∈ arr.filter (fun y => 1 ≤ y ∧ y ≤ 9) := by
        simp [List.mem_filter]
        exact ⟨hx_in, by simp [hx_bounds]⟩
      have hx_sorted : ↑x ∈ (arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) := by
        rw [List.mem_mergeSort]
        exact hx_filtered
      have hx_reversed : ↑x ∈ (arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) |>.reverse := by
        rw [List.mem_reverse]
        exact hx_sorted
      have hx_mapped : digit_to_name ↑x ∈ ((arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) |>.reverse).map digit_to_name := by
        rw [List.mem_map]
        use ↑x
        exact ⟨hx_reversed, rfl⟩
      convert hx_mapped
      rw [← name_to_digit_inverse ↑x]
      · rfl
      · simp [hx_bounds]
    · -- Sorted property
      rw [List.map_reverse]
      have h_sort : List.Sorted (· ≤ ·) (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9) |>.mergeSort (· ≤ ·)) := 
        List.sorted_mergeSort (· ≤ ·) _
      apply List.Sorted.map
      exact h_sort
      intro x y _ _ h_le
      have hx_bounds : 1 ≤ x ∧ x ≤ 9 := by simp [List.mem_filter] at *; assumption
      have hy_bounds : 1 ≤ y ∧ y ≤ 9 := by simp [List.mem_filter] at *; assumption
      simp only [Nat.cast_add, Nat.cast_one]
      rw [digit_name_idxOf x hx_bounds, digit_name_idxOf y hy_bounds]
      omega