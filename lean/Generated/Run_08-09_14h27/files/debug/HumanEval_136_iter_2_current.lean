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
lemma filter_max_some {lst : List Int} {a : Int} :
  lst.filter (· < 0) ≠ [] → 
  a = (lst.filter (· < 0)).foldl max (lst.filter (· < 0)).head! →
  a ∈ lst ∧ a < 0 ∧ ∀ i ∈ lst, i < 0 → i ≤ a := by
  intro h_nonempty h_max
  have h_filter := lst.filter (· < 0)
  have h_head : h_filter.head! ∈ h_filter := by
    simp [List.head!_mem h_nonempty]
  have h_head_mem : h_filter.head! ∈ lst ∧ h_filter.head! < 0 := by
    simp [List.mem_filter] at h_head
    exact h_head
  constructor
  · rw [←h_max]
    have : a ∈ h_filter := by
      rw [h_max]
      apply List.foldl_max_mem
      exact h_nonempty
    simp [List.mem_filter] at this
    exact this.1
  constructor
  · rw [←h_max]
    have : a ∈ h_filter := by
      rw [h_max]
      apply List.foldl_max_mem
      exact h_nonempty
    simp [List.mem_filter] at this
    exact this.2
  · intro i hi_mem hi_neg
    rw [←h_max]
    apply List.le_foldl_max
    simp [List.mem_filter]
    exact ⟨hi_mem, hi_neg⟩

-- LLM HELPER
lemma filter_min_some {lst : List Int} {b : Int} :
  lst.filter (· > 0) ≠ [] → 
  b = (lst.filter (· > 0)).foldl min (lst.filter (· > 0)).head! →
  b ∈ lst ∧ 0 < b ∧ ∀ i ∈ lst, 0 < i → b ≤ i := by
  intro h_nonempty h_min
  have h_filter := lst.filter (· > 0)
  have h_head : h_filter.head! ∈ h_filter := by
    simp [List.head!_mem h_nonempty]
  have h_head_mem : h_filter.head! ∈ lst ∧ 0 < h_filter.head! := by
    simp [List.mem_filter] at h_head
    exact h_head
  constructor
  · rw [←h_min]
    have : b ∈ h_filter := by
      rw [h_min]
      apply List.foldl_min_mem
      exact h_nonempty
    simp [List.mem_filter] at this
    exact this.1
  constructor
  · rw [←h_min]
    have : b ∈ h_filter := by
      rw [h_min]
      apply List.foldl_min_mem
      exact h_nonempty
    simp [List.mem_filter] at this
    exact this.2
  · intro i hi_mem hi_pos
    rw [←h_min]
    apply List.foldl_min_le
    simp [List.mem_filter]
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
      · simp [List.isEmpty_iff_eq_nil] at h_neg
        simp [List.filter_eq_nil_iff] at h_neg
        exact h_neg
      · simp [List.isEmpty_iff_eq_nil] at h_pos
        simp [List.filter_eq_nil_iff] at h_pos
        exact h_pos
    · -- Only negatives empty
      simp [List.isEmpty_iff_eq_nil] at h_neg h_pos
      use (none, some (positives.foldl min positives.head!))
      simp [h_neg, h_pos]
      constructor
      · simp [List.filter_eq_nil_iff] at h_neg
        exact h_neg
      · apply filter_min_some h_pos rfl
  · by_cases h_pos : positives.isEmpty
    · -- Only positives empty
      simp [List.isEmpty_iff_eq_nil] at h_neg h_pos
      use (some (negatives.foldl max negatives.head!), none)
      simp [h_neg, h_pos]
      constructor
      · apply filter_max_some h_neg rfl
      · simp [List.filter_eq_nil_iff] at h_pos
        exact h_pos
    · -- Neither empty
      simp [List.isEmpty_iff_eq_nil] at h_neg h_pos
      use (some (negatives.foldl max negatives.head!), some (positives.foldl min positives.head!))
      simp [h_neg, h_pos]
      constructor
      · apply filter_max_some h_neg rfl
      · apply filter_min_some h_pos rfl