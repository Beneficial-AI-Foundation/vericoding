import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Int → List Int → List Int)
-- inputs
(l1 l2: List Int) :=
let is_unique (result: List Int) :=
  ∀ i j, i < result.length → j < result.length →
  i ≠ j → result[i]! ≠ result[j]!;
let is_sorted (result: List Int) :=
  ∀ i, i < result.length - 1 →
  result[i]! ≤ result[i + 1]!;
-- spec
let spec (result: List Int) :=
  is_unique result ∧
  is_sorted result ∧
  (∀ i : Int, i ∈ result ↔ i ∈ l1 ∧ i ∈ l2)
-- program termination
∃ result, implementation l1 l2 = result ∧
spec result

-- LLM HELPER
def intersection (l1 l2: List Int) : List Int :=
  l1.filter (fun x => x ∈ l2)

-- LLM HELPER
def merge (l1 l2: List Int) : List Int :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1::t1, h2::t2 =>
    if h1 ≤ h2 then h1 :: merge t1 (h2::t2)
    else h2 :: merge (h1::t1) t2

-- LLM HELPER
def merge_sort (l: List Int) : List Int :=
  if l.length ≤ 1 then l
  else
    let mid := l.length / 2
    let left := l.take mid
    let right := l.drop mid
    let sorted_left := merge_sort left
    let sorted_right := merge_sort right
    merge sorted_left sorted_right
termination_by l.length
decreasing_by
  simp_wl
  constructor
  · simp [List.length_take]
    have h_len : 2 ≤ l.length := by omega
    omega
  · simp [List.length_drop]
    have h_len : 2 ≤ l.length := by omega
    omega

-- LLM HELPER
def remove_duplicates (l: List Int) : List Int :=
  match l with
  | [] => []
  | h::t =>
    let rest := remove_duplicates t
    if h ∈ rest then rest else h :: rest

def implementation (l1 l2: List Int) : List Int := 
  merge_sort (remove_duplicates (intersection l1 l2))

-- LLM HELPER
lemma intersection_mem (l1 l2: List Int) : ∀ x, x ∈ intersection l1 l2 ↔ x ∈ l1 ∧ x ∈ l2 := by
  intro x
  simp [intersection, List.mem_filter]

-- LLM HELPER
lemma merge_sorted (l1 l2: List Int) : 
  (∀ i, i < l1.length - 1 → l1[i]! ≤ l1[i + 1]!) →
  (∀ i, i < l2.length - 1 → l2[i]! ≤ l2[i + 1]!) →
  ∀ i, i < (merge l1 l2).length - 1 → (merge l1 l2)[i]! ≤ (merge l1 l2)[i + 1]! := by
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge]
  | case2 l1 => simp [merge]
  | case3 h1 t1 h2 t2 ih =>
    simp [merge]
    split
    · intro h_sorted1 h_sorted2 i hi
      cases i with
      | zero => 
        simp
        have h_le : h1 ≤ h2 := by assumption
        simp [merge]
        split
        · simp
          cases' t1 with t1_h t1_t
          · simp
            exact h_le
          · simp
            have h_sorted1_0 : h1 ≤ t1_h := by
              have := h_sorted1 0 (by simp)
              simp at this
              exact this
            exact h_sorted1_0
        · exact h_le
      | succ i =>
        simp
        apply ih (fun j hj => h_sorted1 (j + 1) (by simp; exact hj)) h_sorted2
        exact hi
    · intro h_sorted1 h_sorted2 i hi
      cases i with
      | zero => 
        simp
        have h_nle : ¬h1 ≤ h2 := by assumption
        have h_le : h2 ≤ h1 := by omega
        simp [merge]
        split
        · exact h_le
        · simp
          cases' t2 with t2_h t2_t
          · simp
            exact h_le
          · simp
            have h_sorted2_0 : h2 ≤ t2_h := by
              have := h_sorted2 0 (by simp)
              simp at this
              exact this
            exact h_sorted2_0
      | succ i =>
        simp
        apply ih h_sorted1 (fun j hj => h_sorted2 (j + 1) (by simp; exact hj))
        exact hi

-- LLM HELPER
lemma merge_sort_sorted (l: List Int) : ∀ i, i < (merge_sort l).length - 1 → (merge_sort l)[i]! ≤ (merge_sort l)[i + 1]! := by
  induction l using merge_sort.induct with
  | case1 l h => 
    simp [merge_sort, h]
  | case2 l h => 
    simp [merge_sort, h]
    intro i hi
    have mid := l.length / 2
    have left := l.take mid
    have right := l.drop mid
    apply merge_sorted
    · exact merge_sort_sorted left
    · exact merge_sort_sorted right
    · exact hi

-- LLM HELPER
lemma merge_mem (l1 l2: List Int) : ∀ x, x ∈ merge l1 l2 ↔ x ∈ l1 ∨ x ∈ l2 := by
  induction l1, l2 using merge.induct with
  | case1 l2 => simp [merge]
  | case2 l1 => simp [merge]
  | case3 h1 t1 h2 t2 ih =>
    simp [merge]
    intro x
    split
    · simp
      constructor
      · intro h
        cases h with
        | inl h => left; left; exact h
        | inr h => 
          have := ih x |>.mp h
          cases this with
          | inl h => left; right; exact h
          | inr h => right; exact h
      · intro h
        cases h with
        | inl h => 
          cases h with
          | inl h => left; exact h
          | inr h => right; exact ih x |>.mpr (Or.inl h)
        | inr h => right; exact ih x |>.mpr (Or.inr h)
    · simp
      constructor
      · intro h
        cases h with
        | inl h => right; left; exact h
        | inr h => 
          have := ih x |>.mp h
          cases this with
          | inl h => left; exact h
          | inr h => right; right; exact h
      · intro h
        cases h with
        | inl h => right; exact ih x |>.mpr (Or.inl h)
        | inr h => 
          cases h with
          | inl h => left; exact h
          | inr h => right; exact ih x |>.mpr (Or.inr h)

-- LLM HELPER
lemma merge_sort_mem (l: List Int) : ∀ x, x ∈ merge_sort l ↔ x ∈ l := by
  induction l using merge_sort.induct with
  | case1 l h => 
    simp [merge_sort, h]
  | case2 l h => 
    simp [merge_sort, h]
    intro x
    have mid := l.length / 2
    have left := l.take mid
    have right := l.drop mid
    rw [merge_mem]
    constructor
    · intro h_mem
      cases h_mem with
      | inl h => 
        have := merge_sort_mem left x |>.mp h
        exact List.mem_of_mem_take this
      | inr h => 
        have := merge_sort_mem right x |>.mp h
        exact List.mem_of_mem_drop this
    · intro h_mem
      have h_partition : x ∈ left ∨ x ∈ right := by
        cases' List.mem_take_or_drop l mid x with h h
        · left; exact h
        · right; exact h
      cases h_partition with
      | inl h => 
        left; exact merge_sort_mem left x |>.mpr h
      | inr h => 
        right; exact merge_sort_mem right x |>.mpr h

-- LLM HELPER
lemma remove_duplicates_unique (l: List Int) : ∀ i j, i < (remove_duplicates l).length → j < (remove_duplicates l).length → i ≠ j → (remove_duplicates l)[i]! ≠ (remove_duplicates l)[j]! := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons h t ih =>
    simp [remove_duplicates]
    intro i j hi hj hij
    split
    · exact ih i j hi hj hij
    · cases i with
      | zero => 
        cases j with
        | zero => contradiction
        | succ j => 
          simp
          have h_not_mem : h ∉ remove_duplicates t := by simp at *; assumption
          have h_mem_j : (remove_duplicates t)[j]! ∈ remove_duplicates t := by
            apply List.getElem_mem
          exact fun h_eq => h_not_mem (h_eq ▸ h_mem_j)
      | succ i =>
        cases j with
        | zero => 
          simp
          have h_not_mem : h ∉ remove_duplicates t := by simp at *; assumption
          have h_mem_i : (remove_duplicates t)[i]! ∈ remove_duplicates t := by
            apply List.getElem_mem
          exact fun h_eq => h_not_mem (h_eq.symm ▸ h_mem_i)
        | succ j =>
          simp
          exact ih i j (by simp at hi; exact hi) (by simp at hj; exact hj) (by simp at hij; exact hij)

-- LLM HELPER
lemma remove_duplicates_subset (l: List Int) : ∀ x, x ∈ remove_duplicates l → x ∈ l := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons h t ih =>
    simp [remove_duplicates]
    intro x hx
    split at hx
    · right; exact ih x hx
    · cases hx with
      | head h_eq => left; exact h_eq
      | tail h_mem => right; exact ih x h_mem

-- LLM HELPER
lemma remove_duplicates_mem (l: List Int) : ∀ x, x ∈ l → x ∈ remove_duplicates l := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons h t ih =>
    simp [remove_duplicates]
    intro x hx
    split
    · cases hx with
      | head h_eq => exact h_eq ▸ (by assumption)
      | tail h_mem => exact ih x h_mem
    · cases hx with
      | head h_eq => left; exact h_eq
      | tail h_mem => right; exact ih x h_mem

theorem correctness
(l1 l2: List Int)
: problem_spec implementation l1 l2
:= by
  simp [problem_spec, implementation]
  use merge_sort (remove_duplicates (intersection l1 l2))
  constructor
  · rfl
  · constructor
    · -- is_unique
      apply remove_duplicates_unique
    · constructor
      · -- is_sorted
        apply merge_sort_sorted
      · -- membership equivalence
        intro i
        constructor
        · intro h
          rw [merge_sort_mem] at h
          have h1 := remove_duplicates_subset _ i h
          exact intersection_mem l1 l2 i |>.mp h1
        · intro h
          rw [merge_sort_mem]
          apply remove_duplicates_mem
          exact intersection_mem l1 l2 i |>.mpr h