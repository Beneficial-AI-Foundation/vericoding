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
      · simp
        have : k = 0 := by linarith [hk, h_k_nonneg]
        exact this
      · constructor
        · exact List.Sorted.nil
        · constructor
          · intro x hx
            simp at hx
          · simp
            have : k = 0 := by linarith [hk, h_k_nonneg]
            exact this
    · simp [hk]
      by_cases hk_large : k.natAbs > arr.length
      · simp [hk_large]
        constructor
        · simp
          have : k.natAbs ≤ arr.length := by
            have k_pos : 0 < k := lt_of_not_le hk
            rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
            rw [← Int.natCast_le] at h_k_le
            exact Int.natCast_le.mp h_k_le
          exfalso
          exact not_le_of_gt hk_large this
        · constructor
          · exact List.Sorted.nil
          · constructor
            · intro x hx
              simp at hx
            · simp
              have : k.natAbs ≤ arr.length := by
                have k_pos : 0 < k := lt_of_not_le hk
                rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
                rw [← Int.natCast_le] at h_k_le
                exact Int.natCast_le.mp h_k_le
              exfalso
              exact not_le_of_gt hk_large this
      · simp [hk_large]
        unfold getTopK
        have k_pos : k > 0 := lt_of_not_le hk
        have k_natAbs_pos : k.natAbs ≠ 0 := by
          rw [Int.natAbs_ne_zero]
          linarith
        simp [k_natAbs_pos]
        constructor
        · rw [List.length_take]
          simp only [min_def, ite_eq_right_iff]
          intro h
          have k_natAbs_eq : k.natAbs = k.toNat := by
            rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
          have k_toNat_le : k.toNat ≤ arr.length := by
            rw [← k_natAbs_eq]
            exact le_of_not_gt hk_large
          rw [k_natAbs_eq] at h ⊢
          have : k = k.toNat := by
            rw [Int.toNat_of_nonneg (le_of_lt k_pos)]
          rw [this]
          exact k_toNat_le
        · constructor
          · apply List.Sorted.mergeSort
          · constructor
            · intro x hx
              have h1 : x ∈ (arr.mergeSort (· ≥ ·)).take k.natAbs := by
                rw [List.mem_mergeSort] at hx
                exact hx
              have h2 : x ∈ arr.mergeSort (· ≥ ·) := List.mem_of_mem_take h1
              rw [List.mem_mergeSort] at h2
              exact h2
            · by_cases hk_zero : k = 0
              · simp [hk_zero]
                have : k.natAbs = 0 := by rw [hk_zero, Int.natAbs_zero]
                simp [this]
              · have k_pos_int : (0 : Int) < k := lt_of_not_le hk
                have k_ne_zero : k ≠ 0 := ne_of_gt k_pos_int
                cases' List.isEmpty_or_exists_mem_of_ne_nil (by
                  rw [List.ne_nil_iff_exists_mem]
                  use arr.head!
                  apply List.head!_mem
                  rw [← List.length_pos_iff_ne_nil]
                  exact h_len_ge) with
                | inl h_empty => 
                  simp at h_empty
                  have : arr.length = 0 := List.length_eq_zero.mpr h_empty
                  linarith [h_len_ge]
                | inr ⟨x, hx⟩ =>
                  simp only [List.reverse_reverse]
                  constructor
                  · have arr_nonempty : arr ≠ [] := List.ne_nil_of_length_pos (by linarith [h_len_ge])
                    rw [List.max?_eq_some_iff]
                    constructor
                    · exact arr_nonempty
                    · intro y hy
                      simp
                  · simp