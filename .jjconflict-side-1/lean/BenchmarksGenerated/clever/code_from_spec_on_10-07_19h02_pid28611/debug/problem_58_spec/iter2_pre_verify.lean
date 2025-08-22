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
    split
    · simp at *
    · omega
  · simp [List.length_drop]
    split
    · simp at *
    · omega
where
  merge (l1 l2: List Int) : List Int :=
    match l1, l2 with
    | [], l2 => l2
    | l1, [] => l1
    | h1::t1, h2::t2 =>
      if h1 ≤ h2 then h1 :: merge t1 (h2::t2)
      else h2 :: merge (h1::t1) t2

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
lemma merge_sort_sorted (l: List Int) : ∀ i, i < (merge_sort l).length - 1 → (merge_sort l)[i]! ≤ (merge_sort l)[i + 1]! := by
  induction l using merge_sort.induct with
  | case1 l h => 
    simp [merge_sort, h]
    intro i hi
    simp at hi
  | case2 l h => 
    simp [merge_sort, h]
    intro i hi
    have h_len : l.length > 1 := by omega
    simp [merge_sort, h] at hi
    have mid := l.length / 2
    have left := l.take mid
    have right := l.drop mid
    have sorted_left := merge_sort left
    have sorted_right := merge_sort right
    have result := merge_sort.merge sorted_left sorted_right
    -- The merge operation preserves sortedness
    have h_merge_sorted : ∀ i, i < result.length - 1 → result[i]! ≤ result[i + 1]! := by
      induction sorted_left, sorted_right using merge_sort.merge.induct with
      | case1 l2 => simp [merge_sort.merge]
      | case2 l1 => simp [merge_sort.merge]
      | case3 h1 t1 h2 t2 ih1 ih2 =>
        simp [merge_sort.merge]
        split
        · simp
          intro i hi
          cases i with
          | zero => simp; split <;> simp
          | succ i => simp; apply ih1; simp at hi; exact hi
        · simp
          intro i hi
          cases i with
          | zero => simp; split <;> simp
          | succ i => simp; apply ih2; simp at hi; exact hi
    exact h_merge_sorted i hi

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
    have h_partition : ∀ y, y ∈ l ↔ y ∈ left ∨ y ∈ right := by
      intro y
      constructor
      · intro hy
        rw [List.mem_take, List.mem_drop] at *
        cases' Nat.lt_or_ge (List.indexOf y l) mid with h h
        · left; exact ⟨hy, h⟩
        · right; exact ⟨hy, h⟩
      · intro hy
        cases hy with
        | inl h => exact List.mem_of_mem_take h
        | inr h => exact List.mem_of_mem_drop h
    have h_merge_mem : ∀ y, y ∈ merge_sort.merge (merge_sort left) (merge_sort right) ↔ y ∈ merge_sort left ∨ y ∈ merge_sort right := by
      intro y
      induction merge_sort left, merge_sort right using merge_sort.merge.induct with
      | case1 l2 => simp [merge_sort.merge]
      | case2 l1 => simp [merge_sort.merge]
      | case3 h1 t1 h2 t2 ih1 ih2 =>
        simp [merge_sort.merge]
        split
        · simp
          constructor
          · intro h
            cases h with
            | inl h => left; left; exact h
            | inr h => exact ih1 y |>.mp h
          · intro h
            cases h with
            | inl h => cases h with
              | inl h => left; exact h
              | inr h => right; exact ih1 y |>.mpr (Or.inl h)
            | inr h => right; exact ih1 y |>.mpr (Or.inr h)
        · simp
          constructor
          · intro h
            cases h with
            | inl h => right; left; exact h
            | inr h => exact ih2 y |>.mp h
          · intro h
            cases h with
            | inl h => right; exact ih2 y |>.mpr (Or.inl h)
            | inr h => cases h with
              | inl h => left; exact h
              | inr h => right; exact ih2 y |>.mpr (Or.inr h)
    rw [h_merge_mem, h_partition]
    simp

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
          simp at hi hj
          have h_not_mem : h ∉ remove_duplicates t := by simp at *; assumption
          have h_mem_j : (remove_duplicates t)[j]! ∈ remove_duplicates t := by
            apply List.get!_mem
            simp at hj
            exact hj
          exact fun h_eq => h_not_mem (h_eq ▸ h_mem_j)
      | succ i =>
        cases j with
        | zero => 
          simp
          simp at hi hj
          have h_not_mem : h ∉ remove_duplicates t := by simp at *; assumption
          have h_mem_i : (remove_duplicates t)[i]! ∈ remove_duplicates t := by
            apply List.get!_mem
            simp at hi
            exact hi
          exact fun h_eq => h_not_mem (h_eq.symm ▸ h_mem_i)
        | succ j =>
          simp
          simp at hi hj hij
          exact ih i j hi hj hij

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
      | inl h_eq => left; exact h_eq
      | inr h_mem => right; exact ih x h_mem

-- LLM HELPER
lemma remove_duplicates_mem (l: List Int) : ∀ x, x ∈ l → x ∈ remove_duplicates l := by
  induction l with
  | nil => simp [remove_duplicates]
  | cons h t ih =>
    simp [remove_duplicates]
    intro x hx
    split
    · cases hx with
      | inl h_eq => exact h_eq ▸ (by assumption)
      | inr h_mem => exact ih x h_mem
    · cases hx with
      | inl h_eq => left; exact h_eq
      | inr h_mem => right; exact ih x h_mem

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