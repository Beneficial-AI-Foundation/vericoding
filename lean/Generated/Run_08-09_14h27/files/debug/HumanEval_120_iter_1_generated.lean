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

-- LLM HELPER
lemma mergeSort_sorted {α : Type*} [LinearOrder α] (l : List α) (r : α → α → Bool) :
  (l.mergeSort r).Sorted (fun a b => r a b = true) := by
  sorry

-- LLM HELPER
lemma mergeSort_perm {α : Type*} [LinearOrder α] (l : List α) (r : α → α → Bool) :
  l.mergeSort r ~ l := by
  sorry

-- LLM HELPER
lemma take_length {α : Type*} (l : List α) (n : Nat) :
  (l.take n).length = min n l.length := by
  sorry

-- LLM HELPER
lemma mem_take {α : Type*} (l : List α) (n : Nat) (x : α) :
  x ∈ l.take n → x ∈ l := by
  sorry

def problem_spec
-- function signature
(impl: List Int → Int → List Int)
-- inputs
(arr: List Int)
(k: Int) :=
-- spec
let spec (result: List Int) :=
    1 ≤ arr.length → arr.length ≤ 1000 → arr.all (fun x => -1000 ≤ x ∧ x ≤ 1000) → 0 ≤ k → k ≤ arr.length →
    result.length = k ∧
    result.Sorted (· ≤ ·) ∧
    ∀ x ∈ result, x ∈ arr ∧

    let result_reversed := result.reverse; -- reverse to get last element
    match result_reversed with
    | [] => k = 0
    | max :: remaining_reversed =>
      arr.max? = some max ∧
      impl (arr.erase max) (k-1) = (remaining_reversed.reverse)
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
        linarith
      · constructor
        · exact List.Sorted.nil
        · constructor
          · intro x hx
            simp at hx
          · simp
            linarith
    · simp [hk]
      by_cases hk_large : k.natAbs > arr.length
      · simp [hk_large]
        constructor
        · simp
          have : k.natAbs ≤ arr.length := by
            rw [Int.natAbs_of_nonneg (le_of_not_gt hk)]
            exact Int.natCast_le.mp h_k_le
          linarith
        · constructor
          · exact List.Sorted.nil
          · constructor
            · intro x hx
              simp at hx
            · simp
              have : k.natAbs ≤ arr.length := by
                rw [Int.natAbs_of_nonneg (le_of_not_gt hk)]
                exact Int.natCast_le.mp h_k_le
              linarith
      · simp [hk_large]
        unfold getTopK
        have k_pos : k > 0 := lt_of_not_ge hk
        have k_natAbs_pos : k.natAbs ≠ 0 := by
          rw [Int.natAbs_ne_zero]
          linarith
        simp [k_natAbs_pos]
        constructor
        · rw [take_length]
          simp [min_def]
          split_ifs with h
          · rw [Int.natAbs_of_nonneg (le_of_lt k_pos)]
          · rw [← Int.natCast_le] at h_k_le
            rw [Int.natAbs_of_nonneg (le_of_not_gt hk)] at h
            linarith
        · constructor
          · apply mergeSort_sorted
          · constructor
            · intro x hx
              have h1 : x ∈ (arr.mergeSort (· ≥ ·)).take k.natAbs := by
                have : (arr.mergeSort (· ≥ ·)).take k.natAbs ~ ((arr.mergeSort (· ≥ ·)).take k.natAbs).mergeSort (· ≤ ·) := by
                  exact (mergeSort_perm _ _).symm
                rw [List.Perm.mem_iff this] at hx
                exact hx
              have h2 : x ∈ arr.mergeSort (· ≥ ·) := mem_take _ _ _ h1
              have h3 : arr.mergeSort (· ≥ ·) ~ arr := mergeSort_perm _ _
              exact List.Perm.mem_iff h3.symm ▸ h2
            · by_cases hk_zero : k = 0
              · simp [hk_zero]
                rw [Int.natAbs_zero]
                simp
              · sorry