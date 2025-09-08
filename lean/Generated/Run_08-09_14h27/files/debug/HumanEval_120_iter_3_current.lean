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
      · have : k = 0 := by linarith [hk, h_k_nonneg]
        rw [this]
        simp
      · constructor
        · exact List.Sorted.nil
        · constructor
          · intro x hx
            simp at hx
          · have : k = 0 := by linarith [hk, h_k_nonneg]
            rw [this]
            simp
    · simp [hk]
      by_cases hk_large : k.natAbs > arr.length
      · simp [hk_large]
        have : k.natAbs ≤ arr.length := by
          have k_pos : 0 < k := lt_of_not_ge hk
          rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
          rw [← Int.natCast_le] at h_k_le
          exact Int.natCast_le.mp h_k_le
        exfalso
        exact not_le_of_gt hk_large this
      · simp [hk_large]
        unfold getTopK
        have k_pos : k > 0 := lt_of_not_ge hk
        have k_natAbs_pos : k.natAbs ≠ 0 := by
          rw [Int.natAbs_ne_zero]
          linarith
        simp [k_natAbs_pos]
        constructor
        · rw [List.length_take]
          have hk_zero : k.natAbs ≤ arr.length := le_of_not_gt hk_large
          rw [min_eq_left hk_zero]
          rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
          rw [Int.toNat_of_nonneg (le_of_lt k_pos)]
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
              · have k_pos_int : (0 : Int) < k := lt_of_not_ge hk
                have k_ne_zero : k ≠ 0 := ne_of_gt k_pos_int
                have arr_nonempty : arr ≠ [] := by
                  rw [← List.length_pos_iff_ne_nil]
                  exact h_len_ge
                have : List.take k.natAbs (arr.mergeSort (· ≥ ·)) ≠ [] := by
                  rw [List.take_ne_nil_iff]
                  constructor
                  · exact le_of_not_gt hk_large
                  · rw [List.length_mergeSort]
                    exact h_len_ge
                rw [List.reverse_ne_nil] at this
                simp
                constructor
                · have : ∃ max, arr.max? = some max := by
                    rw [List.max?_eq_some_iff]
                    exact ⟨arr_nonempty, fun _ _ => le_refl _⟩
                  cases' this with max hmax
                  use max
                  exact hmax
                · simp