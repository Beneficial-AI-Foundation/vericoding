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
  (getLargestK arr k).length = Int.min k arr.length := by
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => simp [getLargestK, Int.min_def]
    | succ n ih =>
      simp [getLargestK]
      cases arr with
      | nil => simp [Int.min_def]
      | cons hd tl =>
        simp [List.isEmpty]
        have : (hd :: tl).max? = some (hd :: tl).max := by simp [List.max?_eq_some_iff]
        simp [this]
        rw [List.length_append, List.length_cons]
        have : (hd :: tl).erase (hd :: tl).max = (hd :: tl).filter (· ≠ (hd :: tl).max) := by
          rw [List.erase_eq_filter]
        simp [this]
        omega
  | neg n =>
    simp [getLargestK, Int.min_def]
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
          have : x ∈ arr.erase (hd :: tl).max := by
            rw [List.erase_eq_filter]
            exact hx
          have : x ∈ hd :: tl := by
            rw [List.mem_erase_iff] at this
            exact this.1
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
          have : x ∈ hd :: tl := by
            have : x ∈ (hd :: tl).erase (hd :: tl).max := by
              rw [List.erase_eq_filter]
              exact ih _ h
            rw [List.mem_erase_iff] at this
            exact this.1
          exact this
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
    · rw [getLargestK_length]
      simp [Int.min_def]
      omega
    constructor
    · exact getLargestK_sorted arr k
    constructor
    · exact getLargestK_mem arr k
    · by_cases hk : k ≤ 0
      · simp [getLargestK, hk]
      · by_cases harr : arr.isEmpty
        · simp [getLargestK, harr]
          cases arr with
          | nil => simp at h1
          | cons => simp at harr
        · exact getLargestK_max_property arr k (by omega) (by cases arr; simp at h1; simp)