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
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => simp [getLargestK]
    | succ n ih =>
      simp [getLargestK]
      cases arr with
      | nil => simp
      | cons hd tl =>
        simp [List.isEmpty]
        have : (hd :: tl).max? = some (hd :: tl).max := by simp [List.max?_eq_some_iff]
        simp [this]
        rw [List.length_append, List.length_cons]
        have h_erase_len : ((hd :: tl).erase (hd :: tl).max).length = (hd :: tl).length - 1 := by
          rw [List.length_erase]
          exact List.max_mem_of_length_pos (by simp)
        rw [h_erase_len]
        simp [Nat.succ_eq_add_one]
        omega
  | neg n =>
    simp [getLargestK]
    omega

-- LLM HELPER
lemma getLargestK_sorted (arr: List Int) (k: Int) : 
  (getLargestK arr k).Sorted (· ≤ ·) := by
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => simp [getLargestK, List.Sorted]
    | succ n ih =>
      simp [getLargestK]
      cases arr with
      | nil => simp [List.Sorted]
      | cons hd tl =>
        simp [List.isEmpty]
        have : (hd :: tl).max? = some (hd :: tl).max := by simp [List.max?_eq_some_iff]
        simp [this]
        apply List.Sorted.append
        · exact ih
        · simp [List.Sorted]
        · intro x hx y hy
          simp at hy
          rw [← hy]
          have : x ∈ getLargestK ((hd :: tl).erase (hd :: tl).max) (Int.ofNat n) := hx
          have : x ∈ (hd :: tl).erase (hd :: tl).max := by
            induction n with
            | zero => simp [getLargestK] at this
            | succ m ihm =>
              simp [getLargestK] at this
              cases h : ((hd :: tl).erase (hd :: tl).max).isEmpty with
              | true => simp [h] at this
              | false =>
                simp [h] at this
                have : ((hd :: tl).erase (hd :: tl).max).max?.isSome := by
                  rw [List.max?_isSome_iff]
                  rw [List.isEmpty_iff_eq_nil] at h
                  exact h
                cases h_max : ((hd :: tl).erase (hd :: tl).max).max? with
                | none => simp [h_max] at this
                | some max_val =>
                  simp [h_max] at this
                  rw [List.mem_append] at this
                  cases this with
                  | inl h1 => 
                    have : x ∈ ((hd :: tl).erase (hd :: tl).max).erase max_val := by
                      exact ih _ h1
                    rw [List.mem_erase_iff] at this
                    exact this.1
                  | inr h2 => 
                    simp at h2
                    rw [← h2]
                    exact List.max_mem_of_length_pos (by simp [List.isEmpty_iff_eq_nil.mp] at h; exact List.length_pos_of_ne_nil h)
          rw [List.mem_erase_iff] at this
          have : x ∈ hd :: tl := this.1
          exact List.le_max_of_mem this
  | neg n =>
    simp [getLargestK, List.Sorted]

-- LLM HELPER
lemma getLargestK_mem (arr: List Int) (k: Int) : 
  ∀ x ∈ getLargestK arr k, x ∈ arr := by
  intro x hx
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => simp [getLargestK] at hx
    | succ n ih =>
      simp [getLargestK] at hx
      cases arr with
      | nil => simp at hx
      | cons hd tl =>
        simp [List.isEmpty] at hx
        have : (hd :: tl).max? = some (hd :: tl).max := by simp [List.max?_eq_some_iff]
        simp [this] at hx
        rw [List.mem_append] at hx
        cases hx with
        | inl h => 
          have : x ∈ (hd :: tl).erase (hd :: tl).max := by
            exact ih _ h
          rw [List.mem_erase_iff] at this
          exact this.1
        | inr h => 
          simp at h
          rw [← h]
          exact List.max_mem_of_length_pos (by simp)
  | neg n =>
    simp [getLargestK] at hx

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
  simp [getLargestK, hk_pos]
  cases arr with
  | nil => simp at harr_pos
  | cons hd tl =>
    simp [List.isEmpty]
    have : (hd :: tl).max? = some (hd :: tl).max := by simp [List.max?_eq_some_iff]
    simp [this]
    have : (getLargestK ((hd :: tl).erase (hd :: tl).max) (k - 1) ++ [(hd :: tl).max]).reverse = 
           (hd :: tl).max :: (getLargestK ((hd :: tl).erase (hd :: tl).max) (k - 1)).reverse := by
      rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.append_nil]
    simp [this]
    constructor
    · rfl
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
    · by_cases hk : k ≤ 0
      · simp [getLargestK, hk]
        omega
      · rw [getLargestK_length]
        · simp [Int.natAbs_of_nonneg h4]
          omega
        · omega
    constructor
    · exact getLargestK_sorted arr k
    constructor
    · exact getLargestK_mem arr k
    · by_cases hk : k ≤ 0
      · simp [getLargestK, hk]
        omega
      · by_cases harr : arr.isEmpty
        · simp [getLargestK, harr]
          cases arr with
          | nil => simp at h1
          | cons => simp at harr
        · exact getLargestK_max_property arr k (by omega) (by cases arr; simp at h1; simp)