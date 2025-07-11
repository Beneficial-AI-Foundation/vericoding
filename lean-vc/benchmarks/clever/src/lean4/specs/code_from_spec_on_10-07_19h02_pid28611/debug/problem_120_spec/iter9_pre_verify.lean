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

-- LLM HELPER
def getLargestK (arr: List Int) (k: Int) : List Int :=
  if k ≤ 0 then []
  else if arr.isEmpty then []
  else
    match arr.max? with
    | none => []
    | some max => 
      let remaining := arr.erase max
      let rest := getLargestK remaining (k - 1)
      rest ++ [max]
termination_by k.natAbs

def implementation (arr: List Int) (k: Int) : List Int := getLargestK arr k

-- LLM HELPER
lemma getLargestK_length (arr: List Int) (k: Int) : 
  k ≥ 0 → (getLargestK arr k).length = min k.natAbs arr.length := by
  intro hk
  induction k using Int.negInduction generalizing arr with
  | nat n =>
    induction n generalizing arr with
    | zero => 
      unfold getLargestK
      simp only [Int.natAbs_zero, min_zero, List.length_nil]
      rw [if_pos (le_refl 0)]
    | succ n ih =>
      unfold getLargestK
      simp only [Int.natAbs_of_nonneg (by omega), Int.natCast_pos, not_le, if_false]
      cases arr with
      | nil => 
        simp only [List.isEmpty_nil, if_true, List.length_nil, min_zero]
      | cons hd tl =>
        simp only [List.isEmpty_cons, if_false]
        cases h : (hd :: tl).max? with
        | none => 
          simp only [List.length_nil, min_zero]
        | some max =>
          simp only [List.length_append, List.length_cons]
          have h_erase_len : ((hd :: tl).erase max).length = (hd :: tl).length - 1 := by
            rw [List.length_erase]
            rw [List.mem_iff_get?]
            rw [List.max?_eq_some_iff] at h
            exact h.1
          rw [ih (by omega), h_erase_len]
          simp only [List.length_cons, Nat.succ_eq_add_one]
          omega
  | neg n =>
    have : k ≤ 0 := by omega
    unfold getLargestK
    simp only [if_pos this, List.length_nil]
    simp only [Int.natAbs_neg, Int.natAbs_of_nonneg (by omega), min_zero]

-- LLM HELPER
lemma getLargestK_sorted (arr: List Int) (k: Int) : 
  (getLargestK arr k).Sorted (· ≤ ·) := by
  induction k using Int.negInduction generalizing arr with
  | nat n =>
    induction n generalizing arr with
    | zero => 
      unfold getLargestK
      simp only [if_pos (le_refl 0)]
      exact List.sorted_nil
    | succ n ih =>
      unfold getLargestK
      simp only [Int.natCast_pos, not_le, if_false]
      cases arr with
      | nil => 
        simp only [List.isEmpty_nil, if_true]
        exact List.sorted_nil
      | cons hd tl =>
        simp only [List.isEmpty_cons, if_false]
        cases h : (hd :: tl).max? with
        | none => 
          exact List.sorted_nil
        | some max =>
          apply List.Sorted.append
          · exact ih
          · exact List.sorted_singleton
          · intro x hx y hy
            simp only [List.mem_singleton] at hy
            rw [← hy]
            have h_mem : x ∈ (hd :: tl).erase max := by
              exact getLargestK_mem ((hd :: tl).erase max) (n + 1 - 1) x hx
            rw [List.mem_erase_iff] at h_mem
            rw [List.max?_eq_some_iff] at h
            exact h.2 x h_mem.1
  | neg n =>
    unfold getLargestK
    simp only [if_pos (by omega)]
    exact List.sorted_nil

-- LLM HELPER
lemma getLargestK_mem (arr: List Int) (k: Int) : 
  ∀ x ∈ getLargestK arr k, x ∈ arr := by
  intro x hx
  induction k using Int.negInduction generalizing arr with
  | nat n =>
    induction n generalizing arr with
    | zero => 
      unfold getLargestK at hx
      simp only [if_pos (le_refl 0), List.not_mem_nil] at hx
    | succ n ih =>
      unfold getLargestK at hx
      simp only [Int.natCast_pos, not_le, if_false] at hx
      cases arr with
      | nil => 
        simp only [List.isEmpty_nil, if_true, List.not_mem_nil] at hx
      | cons hd tl =>
        simp only [List.isEmpty_cons, if_false] at hx
        cases h : (hd :: tl).max? with
        | none => 
          simp only [List.not_mem_nil] at hx
        | some max =>
          rw [h] at hx
          rw [List.mem_append] at hx
          cases hx with
          | inl h_left => 
            have : x ∈ (hd :: tl).erase max := by
              exact ih _ h_left
            rw [List.mem_erase_iff] at this
            exact this.1
          | inr h_right => 
            simp only [List.mem_singleton] at h_right
            rw [← h_right]
            rw [List.max?_eq_some_iff] at h
            exact h.1
  | neg n =>
    unfold getLargestK at hx
    simp only [if_pos (by omega), List.not_mem_nil] at hx

-- LLM HELPER
lemma getLargestK_max_property (arr: List Int) (k: Int) :
  k > 0 → arr.length > 0 →
  let result := getLargestK arr k
  let result_reversed := result.reverse
  match result_reversed with
  | [] => k = 0
  | max :: remaining_reversed =>
    arr.max? = some max ∧
    getLargestK (arr.erase max) (k-1) = (remaining_reversed.reverse) := by
  intro hk_pos harr_pos
  unfold getLargestK
  rw [if_neg (not_le.mpr hk_pos)]
  cases arr with
  | nil => simp only [List.length_nil, lt_self_iff_false] at harr_pos
  | cons hd tl =>
    simp only [List.isEmpty_cons, if_false]
    cases h : (hd :: tl).max? with
    | none => 
      simp only [List.reverse_nil]
      omega
    | some max =>
      rw [h]
      have : (getLargestK ((hd :: tl).erase max) (k - 1) ++ [max]).reverse = 
             max :: (getLargestK ((hd :: tl).erase max) (k - 1)).reverse := by
        rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.append_nil]
      rw [this]
      constructor
      · exact h
      · rw [List.reverse_reverse]

theorem correctness
(arr: List Int)
(k: Int)
: problem_spec implementation arr k := by
  unfold problem_spec implementation
  use getLargestK arr k
  constructor
  · rfl
  · intro h1 h2 h3 h4 h5
    constructor
    · rw [getLargestK_length]
      · simp only [Int.natAbs_of_nonneg h4]
        omega
      · exact h4
    constructor
    · exact getLargestK_sorted arr k
    · intro x hx
      constructor
      · exact getLargestK_mem arr k x hx
      · by_cases hk : k ≤ 0
        · unfold getLargestK
          rw [if_pos hk, List.reverse_nil]
          omega
        · by_cases harr : arr.isEmpty
          · unfold getLargestK
            rw [if_neg (not_le.mpr (Int.not_le.mp hk)), harr, if_true harr, List.reverse_nil]
            cases arr with
            | nil => 
              rfl
            | cons => 
              simp only [List.isEmpty_cons] at harr
          · exact getLargestK_max_property arr k (by omega) (by cases arr; simp only [List.length_nil, not_lt_zero] at h1; simp only [List.length_cons, Nat.succ_pos])