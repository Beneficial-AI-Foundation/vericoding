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
lemma List.head!_mem_nonempty {α : Type*} [Inhabited α] (lst : List α) (h : lst ≠ []) :
  lst.head! ∈ lst := by
  cases lst with
  | nil => contradiction
  | cons x xs => simp [List.head!]

-- LLM HELPER
lemma List.foldl_max_mem_simple {lst : List Int} {init : Int} :
  lst.foldl max init = init ∨ lst.foldl max init ∈ lst := by
  induction lst generalizing init with
  | nil => left; simp [List.foldl]
  | cons x xs ih =>
    have h := ih (max init x)
    cases h with
    | inl h_eq => 
      right
      simp [List.foldl, h_eq]
      by_cases h_max : init ≤ x
      · simp [max, h_max]; left; rfl
      · simp [max, h_max]; right; exact ⟨x, xs, rfl, h_eq⟩
    | inr h_mem =>
      right
      simp [List.foldl]
      right
      exact h_mem

-- LLM HELPER
lemma List.foldl_min_mem_simple {lst : List Int} {init : Int} :
  lst.foldl min init = init ∨ lst.foldl min init ∈ lst := by
  induction lst generalizing init with
  | nil => left; simp [List.foldl]
  | cons x xs ih =>
    have h := ih (min init x)
    cases h with
    | inl h_eq => 
      right
      simp [List.foldl, h_eq]
      by_cases h_min : init ≤ x
      · simp [min, h_min]; right; exact ⟨x, xs, rfl, h_eq⟩
      · simp [min, h_min]; left; rfl
    | inr h_mem =>
      right
      simp [List.foldl]
      right
      exact h_mem

-- LLM HELPER
lemma List.le_foldl_max_simple {lst : List Int} {x init : Int} :
  x ∈ lst → x ≤ lst.foldl max init := by
  intro h
  induction lst generalizing init with
  | nil => contradiction
  | cons head tail ih =>
    cases h with
    | head => 
      simp [List.foldl]
      by_cases h_le : init ≤ head
      · simp [max, h_le]
        apply le_trans (le_refl head)
        apply le_of_eq
        rfl
      · simp [max, h_le]
        apply le_of_eq
        rfl
    | tail _ h_tail =>
      simp [List.foldl]
      exact ih h_tail

-- LLM HELPER
lemma List.foldl_min_le_simple {lst : List Int} {x init : Int} :
  x ∈ lst → lst.foldl min init ≤ x := by
  intro h
  induction lst generalizing init with
  | nil => contradiction  
  | cons head tail ih =>
    cases h with
    | head => 
      simp [List.foldl]
      by_cases h_le : init ≤ head
      · simp [min, h_le]
        apply le_of_eq
        rfl
      · simp [min, h_le]
        apply le_trans (le_refl init)
        apply le_of_lt
        simp at h_le
        exact h_le
    | tail _ h_tail =>
      simp [List.foldl]
      exact ih h_tail

-- LLM HELPER
lemma List.isEmpty_iff_eq_nil {α : Type*} (lst : List α) : lst.isEmpty ↔ lst = [] := by
  simp [List.isEmpty]

-- LLM HELPER
lemma filter_max_properties {lst : List Int} {a : Int} :
  lst.filter (fun x => decide (x < 0)) ≠ [] → 
  a = (lst.filter (fun x => decide (x < 0))).foldl max (lst.filter (fun x => decide (x < 0))).head! →
  a ∈ lst ∧ a < 0 ∧ ∀ i ∈ lst, i < 0 → i ≤ a := by
  intro h_nonempty h_max
  let h_filter := lst.filter (fun x => decide (x < 0))
  have h_head : h_filter.head! ∈ h_filter := List.head!_mem_nonempty h_filter h_nonempty
  constructor
  · rw [h_max]
    have h_mem := List.foldl_max_mem_simple (lst := h_filter) (init := h_filter.head!)
    cases h_mem with
    | inl h_eq =>
      rw [h_eq]
      rw [List.mem_filter] at h_head
      exact h_head.1
    | inr h_mem =>
      rw [List.mem_filter] at h_mem
      exact h_mem.1
  constructor
  · rw [h_max]
    have h_mem := List.foldl_max_mem_simple (lst := h_filter) (init := h_filter.head!)
    cases h_mem with
    | inl h_eq =>
      rw [h_eq]
      rw [List.mem_filter] at h_head
      simp at h_head
      exact h_head.2
    | inr h_mem =>
      rw [List.mem_filter] at h_mem
      simp at h_mem
      exact h_mem.2
  · intro i hi_mem hi_neg
    rw [h_max]
    apply List.le_foldl_max_simple
    rw [List.mem_filter]
    constructor
    · exact hi_mem
    · simp
      exact hi_neg

-- LLM HELPER
lemma filter_min_properties {lst : List Int} {b : Int} :
  lst.filter (fun x => decide (x > 0)) ≠ [] → 
  b = (lst.filter (fun x => decide (x > 0))).foldl min (lst.filter (fun x => decide (x > 0))).head! →
  b ∈ lst ∧ 0 < b ∧ ∀ i ∈ lst, 0 < i → b ≤ i := by
  intro h_nonempty h_min
  let h_filter := lst.filter (fun x => decide (x > 0))
  have h_head : h_filter.head! ∈ h_filter := List.head!_mem_nonempty h_filter h_nonempty
  constructor
  · rw [h_min]
    have h_mem := List.foldl_min_mem_simple (lst := h_filter) (init := h_filter.head!)
    cases h_mem with
    | inl h_eq =>
      rw [h_eq]
      rw [List.mem_filter] at h_head
      exact h_head.1
    | inr h_mem =>
      rw [List.mem_filter] at h_mem
      exact h_mem.1
  constructor
  · rw [h_min]
    have h_mem := List.foldl_min_mem_simple (lst := h_filter) (init := h_filter.head!)
    cases h_mem with
    | inl h_eq =>
      rw [h_eq]
      rw [List.mem_filter] at h_head
      simp at h_head
      exact h_head.2
    | inr h_mem =>
      rw [List.mem_filter] at h_mem
      simp at h_mem
      exact h_mem.2
  · intro i hi_mem hi_pos
    rw [h_min]
    apply List.foldl_min_le_simple
    rw [List.mem_filter]
    constructor
    · exact hi_mem
    · simp
      exact hi_pos

theorem correctness
(lst: List Int)
: problem_spec implementation lst := by
  unfold problem_spec implementation find_largest_negative find_smallest_positive
  let negatives := lst.filter (fun x => decide (x < 0))
  let positives := lst.filter (fun x => decide (x > 0))
  by_cases h_neg : negatives.isEmpty
  · by_cases h_pos : positives.isEmpty
    · -- Both empty
      use (none, none)
      simp only [if_pos h_neg, if_pos h_pos]
      constructor
      · intro ⟨i, hi_mem, hi_neg⟩
        rw [List.isEmpty_iff_eq_nil] at h_neg
        rw [List.filter_eq_nil] at h_neg
        have := h_neg i hi_mem
        simp at this
        linarith
      · intro ⟨i, hi_mem, hi_pos⟩  
        rw [List.isEmpty_iff_eq_nil] at h_pos
        rw [List.filter_eq_nil] at h_pos
        have := h_pos i hi_mem
        simp at this
        linarith
    · -- Only negatives empty
      have h_pos_ne : positives ≠ [] := by
        rw [List.isEmpty_iff_eq_nil] at h_pos
        exact h_pos
      use (none, some (positives.foldl min positives.head!))
      simp only [if_pos h_neg, if_neg h_pos]
      constructor
      · intro ⟨i, hi_mem, hi_neg⟩
        rw [List.isEmpty_iff_eq_nil] at h_neg
        rw [List.filter_eq_nil] at h_neg
        have := h_neg i hi_mem
        simp at this
        linarith
      · have h_props := filter_min_properties h_pos_ne rfl
        constructor
        · exact h_props.2.1
        constructor  
        · exact h_props.1
        · intro i ⟨hi_mem, hi_pos⟩
          exact h_props.2.2 i hi_mem hi_pos
  · by_cases h_pos : positives.isEmpty
    · -- Only positives empty
      have h_neg_ne : negatives ≠ [] := by
        rw [List.isEmpty_iff_eq_nil] at h_neg
        exact h_neg
      use (some (negatives.foldl max negatives.head!), none)
      simp only [if_neg h_neg, if_pos h_pos]
      constructor
      · have h_props := filter_max_properties h_neg_ne rfl
        constructor
        · exact h_props.2.1
        constructor
        · exact h_props.1
        · intro i ⟨hi_mem, hi_neg⟩
          exact h_props.2.2 i hi_mem hi_neg
      · intro ⟨i, hi_mem, hi_pos⟩
        rw [List.isEmpty_iff_eq_nil] at h_pos
        rw [List.filter_eq_nil] at h_pos
        have := h_pos i hi_mem
        simp at this
        linarith
    · -- Neither empty
      have h_neg_ne : negatives ≠ [] := by
        rw [List.isEmpty_iff_eq_nil] at h_neg
        exact h_neg
      have h_pos_ne : positives ≠ [] := by
        rw [List.isEmpty_iff_eq_nil] at h_pos
        exact h_pos
      use (some (negatives.foldl max negatives.head!), some (positives.foldl min positives.head!))
      simp only [if_neg h_neg, if_neg h_pos]
      constructor
      · have h_props := filter_max_properties h_neg_ne rfl
        constructor
        · exact h_props.2.1
        constructor
        · exact h_props.1
        · intro i ⟨hi_mem, hi_neg⟩
          exact h_props.2.2 i hi_mem hi_neg
      · have h_props := filter_min_properties h_pos_ne rfl
        constructor
        · exact h_props.2.1
        constructor  
        · exact h_props.1
        · intro i ⟨hi_mem, hi_pos⟩
          exact h_props.2.2 i hi_mem hi_pos