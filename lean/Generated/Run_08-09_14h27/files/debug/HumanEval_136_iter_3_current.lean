import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def find_largest_negative (lst: List Int) : Option Int :=
  let negatives := lst.filter (· < 0)
  if negatives.isEmpty then none
  else some (negatives.foldl max negatives.head!)

-- LLM HELPER  
def find_smallest_positive (lst: List Int) : Option Int :=
  let positives := lst.filter (· > 0)
  if positives.isEmpty then none
  else some (positives.foldl min positives.head!)

def implementation (lst: List Int) : (Option Int × Option Int) :=
  (find_largest_negative lst, find_smallest_positive lst)

def problem_spec
-- function signature
(impl: List Int → Option Int × Option Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result: Option Int × Option Int) :=
  let (a, b) := result;
  (match a with
  | none => ¬(∃ i, i ∈ lst ∧ i < 0)
  | some a => a < 0 ∧ a ∈ lst ∧ ∀ i, i ∈ lst ∧ i < 0 → i ≤ a) ∧
  (match b with
  | none => ¬(∃ i, i ∈ lst ∧ 0 < i)
  | some b => 0 < b ∧ b ∈ lst ∧ ∀ i, i ∈ lst ∧ 0 < i → b ≤ i)
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

-- LLM HELPER
lemma List.head!_mem_filter {α : Type*} (lst : List α) (p : α → Bool) (h : lst.filter p ≠ []) :
  (lst.filter p).head! ∈ lst.filter p :=
List.head!_mem h

-- LLM HELPER
lemma List.foldl_max_mem {lst : List Int} {init : Int} :
  lst ≠ [] → lst.foldl max init ∈ init :: lst := by
  intro h
  induction lst with
  | nil => contradiction
  | cons x xs ih =>
    simp [List.foldl]
    by_cases h_xs : xs = []
    · simp [h_xs, List.foldl]
      right
      simp
    · have := ih h_xs
      have : xs.foldl max (max init x) ∈ (max init x) :: xs := this
      cases' this with h1 h2
      · simp [max] at h1
        split at h1
        · right; right; exact h2
        · right; simp; exact h1
      · right; right; exact h2

-- LLM HELPER  
lemma List.foldl_min_mem {lst : List Int} {init : Int} :
  lst ≠ [] → lst.foldl min init ∈ init :: lst := by
  intro h
  induction lst with
  | nil => contradiction
  | cons x xs ih =>
    simp [List.foldl]
    by_cases h_xs : xs = []
    · simp [h_xs, List.foldl]
      right
      simp
    · have := ih h_xs
      have : xs.foldl min (min init x) ∈ (min init x) :: xs := this
      cases' this with h1 h2
      · simp [min] at h1
        split at h1
        · right; simp; exact h1
        · right; right; exact h2
      · right; right; exact h2

-- LLM HELPER
lemma List.le_foldl_max {lst : List Int} {x init : Int} :
  x ∈ lst → x ≤ lst.foldl max init := by
  intro h
  induction lst with
  | nil => contradiction
  | cons y ys ih =>
    cases h with
    | head => 
      simp [List.foldl]
      apply le_max_of_le_right
      by_cases h_ys : ys = []
      · simp [h_ys, List.foldl]
      · apply le_of_le_of_eq (le_max_right _ _)
        rfl
    | tail _ h_tail =>
      simp [List.foldl]
      exact ih h_tail

-- LLM HELPER
lemma List.foldl_min_le {lst : List Int} {x init : Int} :
  x ∈ lst → lst.foldl min init ≤ x := by
  intro h
  induction lst with
  | nil => contradiction
  | cons y ys ih =>
    cases h with
    | head => 
      simp [List.foldl]
      apply min_le_of_right_le
      by_cases h_ys : ys = []
      · simp [h_ys, List.foldl]
      · apply le_of_eq_of_le rfl
        apply min_le_right
    | tail _ h_tail =>
      simp [List.foldl]
      exact ih h_tail

-- LLM HELPER
lemma filter_max_some {lst : List Int} {a : Int} :
  lst.filter (· < 0) ≠ [] → 
  a = (lst.filter (· < 0)).foldl max (lst.filter (· < 0)).head! →
  a ∈ lst ∧ a < 0 ∧ ∀ i ∈ lst, i < 0 → i ≤ a := by
  intro h_nonempty h_max
  have h_filter := lst.filter (· < 0)
  have h_head : h_filter.head! ∈ h_filter := List.head!_mem_filter lst (· < 0) h_nonempty
  have h_head_mem : h_filter.head! ∈ lst ∧ h_filter.head! < 0 := by
    rw [List.mem_filter] at h_head
    exact h_head
  constructor
  · have : a ∈ h_filter := by
      rw [h_max]
      have mem_result := List.foldl_max_mem h_nonempty
      cases mem_result with
      | head => rfl
      | tail _ h_tail => 
        rw [List.mem_filter] at h_tail
        exact h_tail.1
    rw [List.mem_filter] at this
    exact this.1
  constructor
  · have : a ∈ h_filter := by
      rw [h_max]
      have mem_result := List.foldl_max_mem h_nonempty
      cases mem_result with
      | head =>
        rw [List.mem_filter] at h_head_mem
        exact h_head_mem.2
      | tail _ h_tail => 
        rw [List.mem_filter] at h_tail
        exact h_tail.2
    rw [List.mem_filter] at this
    exact this.2
  · intro i hi_mem hi_neg
    rw [h_max]
    apply List.le_foldl_max
    rw [List.mem_filter]
    exact ⟨hi_mem, hi_neg⟩

-- LLM HELPER
lemma filter_min_some {lst : List Int} {b : Int} :
  lst.filter (· > 0) ≠ [] → 
  b = (lst.filter (· > 0)).foldl min (lst.filter (· > 0)).head! →
  b ∈ lst ∧ 0 < b ∧ ∀ i ∈ lst, 0 < i → b ≤ i := by
  intro h_nonempty h_min
  have h_filter := lst.filter (· > 0)
  have h_head : h_filter.head! ∈ h_filter := List.head!_mem_filter lst (· > 0) h_nonempty
  have h_head_mem : h_filter.head! ∈ lst ∧ 0 < h_filter.head! := by
    rw [List.mem_filter] at h_head
    exact h_head
  constructor
  · have : b ∈ h_filter := by
      rw [h_min]
      have mem_result := List.foldl_min_mem h_nonempty
      cases mem_result with
      | head => rfl
      | tail _ h_tail => 
        rw [List.mem_filter] at h_tail
        exact h_tail.1
    rw [List.mem_filter] at this
    exact this.1
  constructor
  · have : b ∈ h_filter := by
      rw [h_min]
      have mem_result := List.foldl_min_mem h_nonempty
      cases mem_result with
      | head =>
        rw [List.mem_filter] at h_head_mem
        exact h_head_mem.2
      | tail _ h_tail => 
        rw [List.mem_filter] at h_tail
        exact h_tail.2
    rw [List.mem_filter] at this
    exact this.2
  · intro i hi_mem hi_pos
    rw [h_min]
    apply List.foldl_min_le
    rw [List.mem_filter]
    exact ⟨hi_mem, hi_pos⟩

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation find_largest_negative find_smallest_positive
  let negatives := lst.filter (· < 0)
  let positives := lst.filter (· > 0)
  by_cases h_neg : negatives.isEmpty
  · by_cases h_pos : positives.isEmpty
    · -- Both empty
      use (none, none)
      simp [h_neg, h_pos]
      constructor
      · rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg
        push_neg at h_neg
        simp [List.not_mem_filter_iff] at h_neg
        exact h_neg
      · rw [List.isEmpty_eq_false_iff_exists_mem] at h_pos  
        push_neg at h_pos
        simp [List.not_mem_filter_iff] at h_pos
        exact h_pos
    · -- Only negatives empty
      rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg h_pos
      push_neg at h_neg
      use (none, some (positives.foldl min positives.head!))
      simp [h_neg, h_pos]
      constructor
      · simp [List.not_mem_filter_iff] at h_neg
        exact h_neg
      · have h_pos_ne : positives ≠ [] := by
          rw [List.isEmpty_eq_false_iff_exists_mem] at h_pos
          intro h_empty
          rw [h_empty] at h_pos
          exact h_pos
        exact filter_min_some h_pos_ne rfl
  · by_cases h_pos : positives.isEmpty
    · -- Only positives empty
      rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg h_pos
      push_neg at h_pos
      use (some (negatives.foldl max negatives.head!), none)
      simp [h_neg, h_pos]
      constructor
      · have h_neg_ne : negatives ≠ [] := by
          rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg
          intro h_empty
          rw [h_empty] at h_neg
          exact h_neg
        exact filter_max_some h_neg_ne rfl
      · simp [List.not_mem_filter_iff] at h_pos
        exact h_pos
    · -- Neither empty
      rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg h_pos
      use (some (negatives.foldl max negatives.head!), some (positives.foldl min positives.head!))
      simp [h_neg, h_pos]
      constructor
      · have h_neg_ne : negatives ≠ [] := by
          rw [List.isEmpty_eq_false_iff_exists_mem] at h_neg
          intro h_empty
          rw [h_empty] at h_neg
          exact h_neg
        exact filter_max_some h_neg_ne rfl
      · have h_pos_ne : positives ≠ [] := by
          rw [List.isEmpty_eq_false_iff_exists_mem] at h_pos
          intro h_empty
          rw [h_empty] at h_pos
          exact h_pos
        exact filter_min_some h_pos_ne rfl