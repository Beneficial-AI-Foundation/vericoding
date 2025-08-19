import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → Int → List Int)
(arr: List Int)
(k: Int) :=
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
      implementation (arr.erase max) (k-1) = (remaining_reversed.reverse)
∃ result, implementation arr k = result ∧
spec result

def implementation (arr: List Int) (k: Int) : List Int := 
  if k ≤ 0 then []
  else match arr.max? with
    | none => []
    | some max => (implementation (arr.erase max) (k-1)) ++ [max]

-- LLM HELPER
lemma max_mem_of_max_some {arr : List Int} {max : Int} (h : arr.max? = some max) : max ∈ arr := by
  rw [List.max?_eq_some_iff] at h
  exact h.1

-- LLM HELPER
lemma erase_length_lt {arr : List Int} {max : Int} (h : max ∈ arr) : (arr.erase max).length < arr.length := by
  exact List.length_erase_lt_of_mem h

-- LLM HELPER
lemma erase_max_subset {arr : List Int} {max : Int} : ∀ x ∈ arr.erase max, x ∈ arr := by
  intros x hx
  exact List.mem_of_mem_erase hx

-- LLM HELPER
lemma implementation_length (arr : List Int) (k : Int) : 
  0 ≤ k → k ≤ arr.length → (implementation arr k).length = k.natAbs := by
  intro hk_nonneg hk_le
  induction arr using List.strongInductionOn generalizing k
  case ind arr ih =>
    unfold implementation
    by_cases hk : k ≤ 0
    · simp [hk]
      rw [Int.natAbs_of_nonpos hk]
    · push_neg at hk
      cases' h_max : arr.max? with max
      · simp [h_max]
        have : arr = [] := by
          by_contra h_ne
          have : arr.length > 0 := List.length_pos_of_ne_nil h_ne
          have : ∃ x, x ∈ arr := List.exists_mem_of_length_pos this
          cases' this with x hx
          have : arr.max?.isSome := List.max?_isSome_of_mem hx
          rw [h_max] at this
          simp at this
        simp [this] at hk_le
        have : k = 0 := by omega
        contradiction
      · simp [h_max]
        have h_max_mem : max ∈ arr := max_mem_of_max_some h_max
        have h_erase_lt : (arr.erase max).length < arr.length := erase_length_lt h_max_mem
        have h_k_minus_one : k - 1 ≤ (arr.erase max).length := by
          have : (arr.erase max).length = arr.length - 1 := by
            rw [List.length_erase_of_mem h_max_mem]
          rw [this]
          omega
        have h_k_minus_one_nonneg : 0 ≤ k - 1 := by omega
        have ih_result := ih (arr.erase max) h_erase_lt (k - 1) h_k_minus_one_nonneg h_k_minus_one
        rw [ih_result]
        simp [Int.natAbs_of_nonneg hk_nonneg]
        omega

-- LLM HELPER
lemma implementation_sorted (arr : List Int) (k : Int) : 
  (implementation arr k).Sorted (· ≤ ·) := by
  induction arr using List.strongInductionOn generalizing k
  case ind arr ih =>
    unfold implementation
    by_cases hk : k ≤ 0
    · simp [hk]
      exact List.sorted_nil
    · push_neg at hk
      cases' h_max : arr.max? with max
      · simp [h_max]
        exact List.sorted_nil
      · simp [h_max]
        have h_max_mem : max ∈ arr := max_mem_of_max_some h_max
        have h_erase_lt : (arr.erase max).length < arr.length := erase_length_lt h_max_mem
        have ih_result := ih (arr.erase max) h_erase_lt (k - 1)
        rw [List.sorted_append]
        constructor
        · exact ih_result
        · constructor
          · exact List.sorted_singleton max
          · intro x hx y hy
            simp at hy
            rw [← hy]
            have : x ∈ arr.erase max := by
              have : x ∈ implementation (arr.erase max) (k - 1) := hx
              sorry -- need to prove elements of implementation are in original list
            have : x ∈ arr := erase_max_subset this
            have : x ≤ max := by
              rw [List.max?_eq_some_iff] at h_max
              exact h_max.2 x this
            exact this

-- LLM HELPER
lemma implementation_mem (arr : List Int) (k : Int) : 
  ∀ x ∈ implementation arr k, x ∈ arr := by
  intro x hx
  induction arr using List.strongInductionOn generalizing k
  case ind arr ih =>
    unfold implementation at hx
    by_cases hk : k ≤ 0
    · simp [hk] at hx
    · push_neg at hk
      cases' h_max : arr.max? with max
      · simp [h_max] at hx
      · simp [h_max] at hx
        have h_max_mem : max ∈ arr := max_mem_of_max_some h_max
        have h_erase_lt : (arr.erase max).length < arr.length := erase_length_lt h_max_mem
        rw [List.mem_append] at hx
        cases' hx with hx hx
        · have : x ∈ arr.erase max := ih (arr.erase max) h_erase_lt (k - 1) x hx
          exact erase_max_subset this
        · simp at hx
          rw [← hx]
          exact h_max_mem

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  unfold problem_spec
  use implementation arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5
    constructor
    · sorry -- length equality needs Int.natAbs conversion
    · constructor
      · exact implementation_sorted arr k
      · constructor
        · exact implementation_mem arr k
        · by_cases hk : k = 0
          · simp [hk]
            unfold implementation
            simp [hk]
          · sorry -- need to prove the recursive property