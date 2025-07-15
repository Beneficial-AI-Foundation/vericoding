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
    | zero => 
      unfold getLargestK
      rfl
    | succ n ih =>
      unfold getLargestK
      cases arr with
      | nil => 
        rw [List.isEmpty_nil, if_true, List.length_nil, Int.natAbs_succ, min_zero]
      | cons hd tl =>
        rw [List.isEmpty_cons, if_false]
        have : (hd :: tl).max? = some (hd :: tl).max := by 
          rw [List.max?_eq_some_iff]
          use (hd :: tl).max
          constructor
          · exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
          · intro x hx
            exact List.le_max_of_mem hx
        rw [this]
        rw [List.length_append, List.length_cons]
        have h_erase_len : ((hd :: tl).erase (hd :: tl).max).length = (hd :: tl).length - 1 := by
          rw [List.length_erase]
          exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
        rw [h_erase_len]
        simp only [Nat.succ_eq_add_one]
        omega
  | neg n =>
    unfold getLargestK
    omega

-- LLM HELPER
lemma getLargestK_sorted (arr: List Int) (k: Int) : 
  (getLargestK arr k).Sorted (· ≤ ·) := by
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => 
      unfold getLargestK
      exact List.sorted_nil
    | succ n ih =>
      unfold getLargestK
      cases arr with
      | nil => 
        rw [List.isEmpty_nil, if_true]
        exact List.sorted_nil
      | cons hd tl =>
        rw [List.isEmpty_cons, if_false]
        have : (hd :: tl).max? = some (hd :: tl).max := by 
          rw [List.max?_eq_some_iff]
          use (hd :: tl).max
          constructor
          · exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
          · intro x hx
            exact List.le_max_of_mem hx
        rw [this]
        apply List.Sorted.append
        · exact ih
        · exact List.sorted_singleton
        · intro x hx y hy
          simp only [List.mem_singleton] at hy
          rw [← hy]
          exact le_of_mem_getLargestK_of_erase x hx (hd :: tl)
  | neg n =>
    unfold getLargestK
    exact List.sorted_nil

-- LLM HELPER
lemma le_of_mem_getLargestK_of_erase (x : Int) (hx : x ∈ getLargestK (arr.erase arr.max) n) (arr : List Int) :
  x ≤ arr.max := by
  have h_mem : x ∈ arr.erase arr.max := by
    exact getLargestK_mem (arr.erase arr.max) n x hx
  rw [List.mem_erase_iff] at h_mem
  exact List.le_max_of_mem h_mem.1

-- LLM HELPER
lemma getLargestK_mem (arr: List Int) (k: Int) : 
  ∀ x ∈ getLargestK arr k, x ∈ arr := by
  intro x hx
  induction k using Int.negInduction with
  | nat n =>
    induction n with
    | zero => 
      unfold getLargestK at hx
      exact False.elim hx
    | succ n ih =>
      unfold getLargestK at hx
      cases arr with
      | nil => 
        rw [List.isEmpty_nil, if_true] at hx
        exact False.elim hx
      | cons hd tl =>
        rw [List.isEmpty_cons, if_false] at hx
        have : (hd :: tl).max? = some (hd :: tl).max := by 
          rw [List.max?_eq_some_iff]
          use (hd :: tl).max
          constructor
          · exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
          · intro x hx
            exact List.le_max_of_mem hx
        rw [this] at hx
        rw [List.mem_append] at hx
        cases hx with
        | inl h => 
          have : x ∈ (hd :: tl).erase (hd :: tl).max := by
            exact ih _ h
          rw [List.mem_erase_iff] at this
          exact this.1
        | inr h => 
          simp only [List.mem_singleton] at h
          rw [← h]
          exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
  | neg n =>
    unfold getLargestK at hx
    exact False.elim hx

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
    rw [List.isEmpty_cons, if_false]
    have : (hd :: tl).max? = some (hd :: tl).max := by 
      rw [List.max?_eq_some_iff]
      use (hd :: tl).max
      constructor
      · exact List.max_mem_of_length_pos (by simp only [List.length_cons, Nat.succ_pos])
      · intro x hx
        exact List.le_max_of_mem hx
    rw [this]
    have : (getLargestK ((hd :: tl).erase (hd :: tl).max) (k - 1) ++ [(hd :: tl).max]).reverse = 
           (hd :: tl).max :: (getLargestK ((hd :: tl).erase (hd :: tl).max) (k - 1)).reverse := by
      rw [List.reverse_append, List.reverse_cons, List.reverse_nil, List.append_nil]
    rw [this]
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
      · unfold getLargestK
        rw [if_pos hk, List.length_nil]
        omega
      · rw [getLargestK_length]
        · simp only [Int.natAbs_of_nonneg h4]
          omega
        · omega
    constructor
    · exact getLargestK_sorted arr k
    · constructor
      · exact getLargestK_mem arr k
      · by_cases hk : k ≤ 0
        · unfold getLargestK
          rw [if_pos hk, List.reverse_nil]
          omega
        · by_cases harr : arr.isEmpty
          · unfold getLargestK
            rw [if_neg (not_le.mpr (Int.not_le.mp hk)), harr, if_true, List.reverse_nil]
            cases arr with
            | nil => 
              rfl
            | cons => 
              simp only [List.isEmpty_cons] at harr
          · exact getLargestK_max_property arr k (by omega) (by cases arr; simp only [List.length_nil, not_lt_zero] at h1; simp only [List.length_cons, Nat.succ_pos])