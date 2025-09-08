/- 
function_signature: "def search(numbers: List[int]) -> int"
docstring: |
    You are given a non-empty list of positive integers. Return the greatest integer that is greater than
    zero, and has a frequency greater than or equal to the value of the integer itself.
    The frequency of an integer is the number of times it appears in the list.
    If no such a value exist, return -1.
test_cases:
  - input: [4, 1, 2, 2, 3, 1]
    expected_output: 2
  - input: [1, 2, 2, 3, 3, 3, 4, 4, 4]
    expected_output: 3
  - input: [5, 5, 4, 4, 4]
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def satisfies_condition (numbers: List Int) (x: Int) : Bool :=
  x > 0 && (numbers.count x) ≥ x

-- LLM HELPER
def get_valid_numbers (numbers: List Int) : List Int :=
  (numbers.toFinset.toList).filter (satisfies_condition numbers)

def implementation (numbers: List Int) : (Int) :=
  let valid := get_valid_numbers numbers
  if valid.isEmpty then -1
  else valid.maximum.getD (-1)

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: Int) :=
0 < numbers.length ∧ numbers.all (fun n => 0 < n) →
(result ≠ -1 ↔ ∃ i : Nat, i < numbers.length ∧
  numbers[i]! = result ∧ numbers[i]! > 0 ∧
  numbers[i]! ≤ (numbers.filter (fun x => x = numbers[i]!)).length ∧
  (¬∃ j : Nat, j < numbers.length ∧
  numbers[i]! < numbers[j]! ∧ numbers[j]! ≤ numbers.count numbers[j]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma count_filter_eq (numbers: List Int) (x: Int) :
  (numbers.filter (fun y => y = x)).length = numbers.count x := by
  simp [List.count_eq_length_filter]

-- LLM HELPER  
lemma satisfies_condition_iff (numbers: List Int) (x: Int) :
  satisfies_condition numbers x ↔ (x > 0 ∧ numbers.count x ≥ x) := by
  simp [satisfies_condition]
  constructor
  · intro h
    cases' h with h1 h2
    exact ⟨Int.zero_lt_iff_zero_lt_natCast.mp h1, Int.natCast_le_iff_le.mp h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨Int.zero_lt_iff_zero_lt_natCast.mpr h1, Int.natCast_le_iff_le.mpr h2⟩

-- LLM HELPER
lemma mem_get_valid_numbers_iff (numbers: List Int) (x: Int) :
  x ∈ get_valid_numbers numbers ↔ (x ∈ numbers ∧ x > 0 ∧ numbers.count x ≥ x) := by
  simp [get_valid_numbers, satisfies_condition_iff]
  constructor
  · intro ⟨h1, h2, h3⟩
    exact ⟨List.mem_toList.mp h1, h2, h3⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨List.mem_toList.mpr (List.mem_toFinset.mpr h1), h2, h3⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro ⟨hlen, hpos⟩
    simp [implementation]
    constructor
    · intro h
      by_cases hempty : (get_valid_numbers numbers).isEmpty
      · simp [hempty] at h
      · simp [hempty] at h
        have hmax := List.maximum_mem (by simp [List.isEmpty_iff_eq_nil.mp hempty])
        rw [mem_get_valid_numbers_iff] at hmax
        cases' hmax with hmem hcond
        cases' hcond with hpos_max hcount
        use List.findIdx (· = (get_valid_numbers numbers).maximum.getD (-1)) numbers
        constructor
        · by_contra hnot
          simp at hnot
          have := List.findIdx_lt_length_of_exists ⟨hmem⟩
          exact hnot this
        · constructor
          · simp [List.get_findIdx hmem]
            exact List.maximum_getD_mem (by simp [List.isEmpty_iff_eq_nil.mp hempty])
          · constructor
            · exact hpos_max
            · constructor
              · rw [count_filter_eq]
                exact hcount
              · intro j hj hlt hle
                have hj_in : numbers[j]! ∈ get_valid_numbers numbers := by
                  rw [mem_get_valid_numbers_iff]
                  constructor
                  · exact List.getElem_mem numbers j hj
                  · constructor
                    · by_contra hneg
                      simp at hneg
                      have := hpos j hj
                      simp at this
                      exact Int.lt_irrefl _ (Int.lt_of_le_of_lt (Int.le_of_not_gt hneg) this)
                    · exact hle
                have hmax_ge := List.le_maximum_of_mem hj_in (by simp [List.isEmpty_iff_eq_nil.mp hempty])
                exact Int.lt_irrefl _ (Int.lt_of_lt_of_le hlt hmax_ge)
    · intro ⟨i, hi, heq, hpos_i, hcount_i, hmax_i⟩
      by_cases hempty : (get_valid_numbers numbers).isEmpty
      · simp [hempty]
        have : numbers[i]! ∈ get_valid_numbers numbers := by
          rw [mem_get_valid_numbers_iff]
          constructor
          · exact List.getElem_mem numbers i hi
          · constructor
            · exact hpos_i
            · rw [← count_filter_eq]
              exact hcount_i
        simp [get_valid_numbers, List.isEmpty_iff_eq_nil] at hempty this
      · simp [hempty]
        have hvalid : numbers[i]! ∈ get_valid_numbers numbers := by
          rw [mem_get_valid_numbers_iff]
          constructor
          · exact List.getElem_mem numbers i hi
          · constructor
            · exact hpos_i
            · rw [← count_filter_eq]
              exact hcount_i
        have hmax_ge := List.le_maximum_of_mem hvalid (by simp [List.isEmpty_iff_eq_nil.mp hempty])
        have hmax_valid : (get_valid_numbers numbers).maximum.getD (-1) ∈ get_valid_numbers numbers :=
          List.maximum_getD_mem (by simp [List.isEmpty_iff_eq_nil.mp hempty])
        rw [mem_get_valid_numbers_iff] at hmax_valid
        cases' hmax_valid with hmem_max hcond_max
        cases' hcond_max with hpos_max hcount_max
        by_contra hcontra
        simp at hcontra
        have hlt : numbers[i]! < (get_valid_numbers numbers).maximum.getD (-1) := 
          Int.lt_of_le_of_ne hmax_ge hcontra
        exact hmax_i ⟨List.findIdx (· = (get_valid_numbers numbers).maximum.getD (-1)) numbers,
          List.findIdx_lt_length_of_exists ⟨hmem_max⟩, 
          List.get_findIdx hmem_max, hlt, hcount_max⟩

-- #test implementation [4, 1, 2, 2, 3, 1] = 2
-- #test implementation [1, 2, 2, 3, 3, 4, 4, 4] = 3
-- #test implementation [5, 5, 4, 4, 4] = -1