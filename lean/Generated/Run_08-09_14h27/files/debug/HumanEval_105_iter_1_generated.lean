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
  apply List.length_filter_le

-- LLM HELPER
lemma sorted_reverse_property (l: List Int) :
  List.Sorted Int.le l → List.Sorted Int.ge l.reverse := by
  intro h
  rw [List.sorted_reverse_iff]
  exact h

-- LLM HELPER  
lemma name_to_digit_inverse (x: Int) (h: 1 ≤ x ∧ x ≤ 9) :
  let digits := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  digits[x-1]! = digit_to_name x := by
  cases' h with h1 h2
  interval_cases x <;> simp [digit_to_name]

-- LLM HELPER
lemma digit_name_idxOf (x: Int) (h: 1 ≤ x ∧ x ≤ 9) :
  let digits := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
  List.idxOf (digit_to_name x) digits + 1 = x := by
  cases' h with h1 h2
  interval_cases x <;> simp [digit_to_name, List.idxOf]

theorem correctness
(arr: List Int)
: problem_spec implementation arr := by
  use implementation arr
  constructor
  · rfl
  · simp [implementation]
    let filtered := arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)
    let sorted := filtered.mergeSort (· ≤ ·)
    let reversed := sorted.reverse
    let result := reversed.map digit_to_name
    constructor
    · -- All strings in result are in digits
      intro s hs
      simp at hs
      obtain ⟨x, hx_in, hx_eq⟩ := hs
      rw [← hx_eq]
      have hx_bounds : x ∈ filtered := by
        simp [filtered] at hx_in
        exact List.mem_of_mem_reverse hx_in
      simp [filtered] at hx_bounds
      obtain ⟨_, hx_filter⟩ := hx_bounds
      exact digit_to_name_in_digits x hx_filter
    constructor
    · -- Length constraint
      simp [result, reversed, sorted, filtered]
      have h1 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).length ≤ arr.length := filter_length_le arr
      have h2 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).length := List.length_mergeSort _ _
      have h3 : (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.length := List.length_reverse _
      have h4 : ((arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.map digit_to_name).length = (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9)).mergeSort (· ≤ ·) |>.reverse.length := List.length_map _ _
      rw [h4, h3, h2]
      exact h1
    constructor
    · -- All valid digits appear in result
      intro x hx
      simp [result, reversed, sorted, filtered]
      cases' hx with hx_in hx_bounds
      have hx_filtered : x ∈ arr.filter (fun y => 1 ≤ y ∧ y ≤ 9) := by
        simp [List.mem_filter]
        exact ⟨hx_in, hx_bounds⟩
      have hx_sorted : x ∈ (arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) := by
        rw [List.mem_mergeSort]
        exact hx_filtered
      have hx_reversed : x ∈ (arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) |>.reverse := by
        rw [List.mem_reverse]
        exact hx_sorted
      have hx_mapped : digit_to_name x ∈ ((arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)).mergeSort (· ≤ ·) |>.reverse).map digit_to_name := by
        rw [List.mem_map]
        use x
        exact ⟨hx_reversed, rfl⟩
      convert hx_mapped
      rw [name_to_digit_inverse]
      constructor <;> simp at hx_bounds <;> exact hx_bounds
    · -- Sorted property
      simp [result, reversed, sorted, filtered]
      let digits := ["One", "Two", "Three", "Four", "Five", "Six", "Seven", "Eight", "Nine"]
      have h_sort : List.Sorted (· ≤ ·) (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9) |>.mergeSort (· ≤ ·)) := 
        List.sorted_mergeSort (· ≤ ·) _
      have h_map_eq : List.map (fun s => List.idxOf s digits + 1) 
        ((arr.filter (fun x => 1 ≤ x ∧ x ≤ 9) |>.mergeSort (· ≤ ·)).reverse.map digit_to_name) = 
        (arr.filter (fun x => 1 ≤ x ∧ x ≤ 9) |>.mergeSort (· ≤ ·)).reverse := by
        rw [List.map_map]
        congr 1
        ext x
        simp
        have hx_bounds : x ∈ arr.filter (fun y => 1 ≤ y ∧ y ≤ 9) → 1 ≤ x ∧ x ≤ 9 := by
          intro h
          simp [List.mem_filter] at h
          exact h.2
        by_cases h : x ∈ arr.filter (fun y => 1 ≤ y ∧ y ≤ 9)
        · have hb := hx_bounds h
          exact digit_name_idxOf x hb
        · rfl
      rw [h_map_eq, List.reverse_reverse]
      exact h_sort

-- #test implementation [2, 1, 1, 4, 5, 8, 2, 3] = ["Eight", "Five", "Four", "Three", "Two", "Two", "One", "One"]
-- #test implementation [] = []
-- #test implementation [1, -1 , 55] = ["One"]
-- #test implementation [1, -1, 3, 2] = ["Three", "Two", "One"]
-- #test implementation [9, 4, 8] = ["Nine", "Eight", "Four"]