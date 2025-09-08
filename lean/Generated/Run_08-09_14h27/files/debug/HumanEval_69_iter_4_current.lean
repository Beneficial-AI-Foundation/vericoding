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
  x > 0 && (numbers.count x) ≥ Int.natAbs x

-- LLM HELPER
noncomputable def get_valid_numbers (numbers: List Int) : List Int :=
  (numbers.toFinset.toList).filter (satisfies_condition numbers)

noncomputable def implementation (numbers: List Int) : (Int) :=
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
lemma filter_eq_count (numbers: List ℤ) (x: ℤ) :
  (List.filter (fun y => decide (y = x)) numbers).length = (List.filter (fun x_1 => x_1 == x) numbers).length := by
  simp only [List.length_filter]
  congr
  ext y
  simp only [decide_eq_true_eq]
  rw [beq_iff_eq]

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers := by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · intro ⟨hlen, hpos⟩
    constructor
    · intro h
      simp [implementation] at h
      by_cases hempty : (get_valid_numbers numbers).isEmpty
      · simp [hempty] at h
        exfalso
        exact h
      · simp [hempty] at h
        have hmax_mem : (get_valid_numbers numbers).maximum.getD (-1) ∈ get_valid_numbers numbers := by
          apply List.maximum_getD_mem
          rw [← List.isEmpty_iff_eq_nil]
          exact hempty
        simp [get_valid_numbers, satisfies_condition] at hmax_mem
        have ⟨hmem, hcond⟩ := hmax_mem
        have hidx : ∃ i, i < numbers.length ∧ numbers[i]! = (get_valid_numbers numbers).maximum.getD (-1) := by
          have h_in_orig : (get_valid_numbers numbers).maximum.getD (-1) ∈ numbers := by
            have h_subset : get_valid_numbers numbers ⊆ numbers := by
              intro x hx
              simp [get_valid_numbers] at hx
              exact List.mem_of_mem_toFinset hx.1
            exact h_subset hmem
          obtain ⟨i, hi_lt, hi_eq⟩ := List.mem_iff_get.mp h_in_orig
          use i
          constructor
          · exact hi_lt
          · rw [List.getElem_eq_get]
            exact hi_eq.symm
        obtain ⟨i, hi_lt, hi_eq⟩ := hidx
        use i
        constructor
        · exact hi_lt
        constructor
        · exact hi_eq.trans h
        constructor
        · simp [satisfies_condition] at hcond
          exact hcond.1
        constructor
        · simp [satisfies_condition] at hcond
          rw [← hi_eq, ← h]
          rw [count_filter_eq]
          have hpos_val : 0 < (get_valid_numbers numbers).maximum.getD (-1) := hcond.1
          have hcount_ge : numbers.count ((get_valid_numbers numbers).maximum.getD (-1)) ≥ Int.natAbs ((get_valid_numbers numbers).maximum.getD (-1)) := hcond.2
          have hnat_abs_eq : Int.natAbs ((get_valid_numbers numbers).maximum.getD (-1)) = ((get_valid_numbers numbers).maximum.getD (-1)).natAbs := rfl
          rw [hnat_abs_eq] at hcount_ge
          have hpos_nat : ((get_valid_numbers numbers).maximum.getD (-1)).natAbs = Int.natAbs ((get_valid_numbers numbers).maximum.getD (-1)) := by
            simp [Int.natAbs]
          rw [← hpos_nat] at hcount_ge
          exact Int.le_natCast_of_natCast_le hcount_ge
        · intro j hj_lt hj_gt
          by_contra hcontra
          push_neg at hcontra
          simp [satisfies_condition] at hcond
          have hj_satisfies : satisfies_condition numbers numbers[j]! := by
            simp [satisfies_condition]
            constructor
            · have hpos_all := List.all_iff_forall.mp hpos
              exact hpos_all numbers[j]! (List.getElem_mem _ _ _)
            · have hcount_bound : numbers.count numbers[j]! ≥ Int.natAbs numbers[j]! := by
                have hpos_j : 0 < numbers[j]! := by
                  have hpos_all := List.all_iff_forall.mp hpos
                  exact hpos_all numbers[j]! (List.getElem_mem _ _ _)
                have hnat_abs_eq : Int.natAbs numbers[j]! = numbers[j]!.natAbs := rfl
                rw [hnat_abs_eq]
                exact Int.natCast_le.mp hcontra
              exact hcount_bound
          have hj_in_valid : numbers[j]! ∈ get_valid_numbers numbers := by
            simp [get_valid_numbers]
            constructor
            · exact List.mem_toFinset.mpr (List.getElem_mem _ _ _)
            · exact hj_satisfies
          have hmax_ge : numbers[j]! ≤ (get_valid_numbers numbers).maximum.getD (-1) := by
            apply List.le_maximum_getD
            exact hj_in_valid
          rw [← hi_eq, ← h] at hmax_ge
          linarith [hj_gt]
    · intro ⟨i, hi_lt, hi_eq, hpos_i, hcount_i, hmax_i⟩
      simp [implementation]
      by_contra h
      simp at h
      have hempty : (get_valid_numbers numbers).isEmpty := by
        by_contra hne
        simp at hne
        have hmax_exists := List.maximum_getD_mem (get_valid_numbers numbers) (-1)
        simp [List.isEmpty_iff_eq_nil] at hne
        have hmax_in := hmax_exists hne
        simp at hmax_in
        exact h
      have hi_satisfies : satisfies_condition numbers numbers[i]! := by
        simp [satisfies_condition]
        constructor
        · exact hpos_i
        · rw [← hi_eq]
          rw [count_filter_eq] at hcount_i
          have hpos_nat : 0 < numbers[i]! := hpos_i
          have hnat_abs_eq : Int.natAbs numbers[i]! = numbers[i]!.natAbs := rfl
          rw [← hnat_abs_eq]
          exact Int.natCast_le.mpr hcount_i
      have hi_in_valid : numbers[i]! ∈ get_valid_numbers numbers := by
        simp [get_valid_numbers]
        constructor
        · exact List.mem_toFinset.mpr (List.getElem_mem _ _ _)
        · exact hi_satisfies
      have hnonempty : ¬(get_valid_numbers numbers).isEmpty := by
        rw [List.isEmpty_iff_eq_nil]
        intro h_nil
        rw [h_nil] at hi_in_valid
        exact hi_in_valid
      exact hnonempty hempty

-- #test implementation [4, 1, 2, 2, 3, 1] = 2
-- #test implementation [1, 2, 2, 3, 3, 4, 4, 4] = 3
-- #test implementation [5, 5, 4, 4, 4] = -1