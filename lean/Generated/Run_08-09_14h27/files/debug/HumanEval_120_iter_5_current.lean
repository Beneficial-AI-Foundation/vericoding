import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def getTopK (arr: List Int) (k: Nat) : List Int :=
  if k = 0 then []
  else
    let sorted := arr.mergeSort (· ≥ ·)
    (sorted.take k).mergeSort (· ≤ ·)

def implementation (arr: List Int) (k: Int) : List Int :=
  if k ≤ 0 then []
  else if k.natAbs > arr.length then []
  else getTopK arr k.natAbs

def problem_spec
-- function signature
(impl: List Int → Int → List Int)
-- inputs
(arr: List Int)
(k: Int) :=
-- spec
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => decide (-1000 ≤ x ∧ x ≤ 1000)) = true → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    (∀ x ∈ result, x ∈ arr) ∧
    (let result_reversed := result.reverse
     match result_reversed with
     | [] => k = 0
     | max :: remaining_reversed =>
       arr.max? = some max ∧
       impl (arr.erase max) (k-1) = (remaining_reversed.reverse))
-- program terminates
∃ result, impl arr k = result ∧
-- return value satisfies spec
spec result

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k  := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h_len_ge h_len_le h_range h_k_nonneg h_k_le
    unfold implementation
    by_cases hk : k ≤ 0
    · simp [hk]
      constructor
      · have : k = 0 := by
          have : k ≤ 0 := hk
          have : 0 ≤ k := h_k_nonneg
          omega
        rw [this]
        simp
      · constructor
        · exact List.Sorted.nil
        · constructor
          · intro x hx
            simp at hx
          · have : k = 0 := by
              have : k ≤ 0 := hk
              have : 0 ≤ k := h_k_nonneg
              omega
            rw [this]
            simp
    · simp [hk]
      by_cases hk_large : k.natAbs > arr.length
      · simp [hk_large]
        have k_pos : 0 < k := lt_of_not_le hk
        have : k.natAbs ≤ arr.length := by
          rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
          have : k ≤ arr.length := h_k_le
          exact Int.coe_nat_le_coe_nat_iff.mp this
        omega
      · simp [hk_large]
        unfold getTopK
        have k_pos : k > 0 := lt_of_not_le hk
        have k_natAbs_pos : k.natAbs ≠ 0 := by
          rw [Int.natAbs_ne_zero]
          linarith
        simp [k_natAbs_pos]
        constructor
        · rw [List.length_take]
          have hk_bound : k.natAbs ≤ arr.length := le_of_not_gt hk_large
          rw [min_eq_left]
          · rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
            exact Int.coe_nat_le_coe_nat_iff.mp h_k_le
          · rw [List.length_mergeSort]
            exact hk_bound
        · constructor
          · apply List.Sorted.mergeSort
          · constructor
            · intro x hx
              rw [List.mem_mergeSort] at hx
              have : x ∈ List.take k.natAbs (arr.mergeSort (· ≥ ·)) := hx
              have : x ∈ arr.mergeSort (· ≥ ·) := List.mem_of_mem_take this
              rw [List.mem_mergeSort] at this
              exact this
            · by_cases hk_zero : k = 0
              · have : k.natAbs = 0 := by rw [hk_zero, Int.natAbs_zero]
                simp [this]
                rw [hk_zero]
                simp
              · have k_pos_int : (0 : Int) < k := lt_of_not_le hk
                have k_ne_zero : k ≠ 0 := ne_of_gt k_pos_int
                have arr_nonempty : arr ≠ [] := by
                  rw [← List.length_pos_iff_ne_nil]
                  exact h_len_ge
                have : List.take k.natAbs (arr.mergeSort (· ≥ ·)) ≠ [] := by
                  rw [← List.length_pos_iff_ne_nil]
                  rw [List.length_take]
                  rw [List.length_mergeSort]
                  rw [min_pos_iff]
                  left
                  rw [Int.natAbs_pos]
                  exact k_ne_zero
                have result_nonempty : (List.take k.natAbs (arr.mergeSort (· ≥ ·))).mergeSort (· ≤ ·) ≠ [] := by
                  rw [← List.length_pos_iff_ne_nil]
                  rw [List.length_mergeSort]
                  rw [← List.length_pos_iff_ne_nil] at this
                  exact this
                simp
                constructor
                · have sorted_desc := List.Sorted.mergeSort arr (· ≥ ·)
                  have max_in_sorted : arr.max? = (arr.mergeSort (· ≥ ·)).head? := by
                    cases h : arr with
                    | nil => simp at h_len_ge
                    | cons head tail =>
                      simp [List.max?]
                      have : (head :: tail).mergeSort (· ≥ ·) ≠ [] := by
                        rw [← List.length_pos_iff_ne_nil]
                        rw [List.length_mergeSort]
                        simp
                        exact h_len_ge
                      cases sorted_eq : (head :: tail).mergeSort (· ≥ ·) with
                      | nil => contradiction
                      | cons max_val rest =>
                        simp [List.head?]
                        have : max_val ∈ (head :: tail) := by
                          rw [← sorted_eq]
                          exact List.mem_mergeSort.mpr (List.mem_cons_self _ _)
                        have max_is_max : ∀ x ∈ (head :: tail), x ≤ max_val := by
                          intro x hx
                          have : x ∈ (head :: tail).mergeSort (· ≥ ·) := List.mem_mergeSort.mpr hx
                          rw [sorted_eq] at this
                          cases this with
                          | head => rfl
                          | tail _ h_in_rest =>
                            have sorted_property : List.Sorted (· ≥ ·) (max_val :: rest) := by
                              rw [← sorted_eq]
                              exact List.Sorted.mergeSort _ _
                            have : max_val ≥ x := by
                              have : List.Pairwise (· ≥ ·) (max_val :: rest) := List.Sorted.pairwise sorted_property
                              exact List.rel_of_pairwise_cons this h_in_rest
                            exact this
                        exact List.max?_eq_some_iff.mpr ⟨List.mem_cons_self _ _, max_is_max⟩
                  have take_starts_with_max : (List.take k.natAbs (arr.mergeSort (· ≥ ·))).head? = (arr.mergeSort (· ≥ ·)).head? := by
                    have k_pos_nat : k.natAbs > 0 := Int.natAbs_pos.mpr k_ne_zero
                    have arr_sorted_nonempty : arr.mergeSort (· ≥ ·) ≠ [] := by
                      rw [← List.length_pos_iff_ne_nil]
                      rw [List.length_mergeSort]
                      exact h_len_ge
                    exact List.head?_take_of_succ arr_sorted_nonempty k_pos_nat
                  have final_contains_max : arr.max? ∈ (List.take k.natAbs (arr.mergeSort (· ≥ ·))).mergeSort (· ≤ ·) := by
                    rw [List.mem_mergeSort]
                    rw [max_in_sorted] at *
                    rw [← take_starts_with_max]
                    have : (List.take k.natAbs (arr.mergeSort (· ≥ ·))).head? ∈ List.take k.natAbs (arr.mergeSort (· ≥ ·)) := by
                      cases h_take : List.take k.natAbs (arr.mergeSort (· ≥ ·)) with
                      | nil => simp at this
                      | cons head tail =>
                        simp [List.head?]
                        exact List.mem_cons_self _ _
                    exact this
                  cases max_case : arr.max? with
                  | none => 
                    simp at max_case
                    rw [List.max?_eq_none_iff] at max_case
                    rw [max_case] at h_len_ge
                    simp at h_len_ge
                  | some max_val =>
                    exact max_case
                · have : k - 1 ≥ 0 := by omega
                  have remaining_length : ((List.take k.natAbs (arr.mergeSort (· ≥ ·))).mergeSort (· ≤ ·)).reverse.tail.reverse.length = k - 1 := by
                    simp [List.length_reverse, List.length_tail]
                    rw [List.length_mergeSort, List.length_take, List.length_mergeSort]
                    rw [min_eq_left (le_of_not_gt hk_large)]
                    have : k.natAbs = Int.natAbs k := rfl
                    rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
                    have k_int_pos : k > 0 := k_pos
                    have : k.natAbs ≥ 1 := by
                      rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
                      omega
                    omega
                  exact remaining_length ▸ rfl