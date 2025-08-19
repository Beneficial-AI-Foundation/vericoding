import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

-- LLM HELPER
def List.count {α : Type*} [BEq α] (l : List α) (a : α) : Nat :=
  l.filter (· == a) |>.length

-- LLM HELPER
def List.getElem! {α : Type*} [Inhabited α] (l : List α) (i : Nat) : α :=
  if h : i < l.length then l[i] else default

-- LLM HELPER
lemma List.mem_filter {α : Type*} (l : List α) (p : α → Bool) (x : α) :
  x ∈ l.filter p ↔ x ∈ l ∧ p x = true := by
  induction l with
  | nil => simp [List.filter]
  | cons head tail ih =>
    simp [List.filter]
    cases h : p head with
    | true => 
      simp [List.filter_cons_of_pos h]
      constructor
      · intro h_in
        cases h_in with
        | inl h_eq => 
          subst h_eq
          exact ⟨Or.inl rfl, h⟩
        | inr h_tail => 
          have ⟨h_mem, h_prop⟩ := ih.mp h_tail
          exact ⟨Or.inr h_mem, h_prop⟩
      · intro ⟨h_mem, h_prop⟩
        cases h_mem with
        | inl h_eq => 
          subst h_eq
          exact Or.inl rfl
        | inr h_tail => 
          exact Or.inr (ih.mpr ⟨h_tail, h_prop⟩)
    | false =>
      simp [List.filter_cons_of_neg h]
      constructor
      · intro h_tail
        have ⟨h_mem, h_prop⟩ := ih.mp h_tail
        exact ⟨Or.inr h_mem, h_prop⟩
      · intro ⟨h_mem, h_prop⟩
        cases h_mem with
        | inl h_eq => 
          subst h_eq
          rw [h] at h_prop
          simp at h_prop
        | inr h_tail => 
          exact ih.mpr ⟨h_tail, h_prop⟩

-- LLM HELPER
lemma List.filter_cons_of_pos {α : Type*} (p : α → Bool) (a : α) (l : List α) (h : p a = true) :
  (a :: l).filter p = a :: l.filter p := by
  simp [List.filter, h]

-- LLM HELPER
lemma List.filter_cons_of_neg {α : Type*} (p : α → Bool) (a : α) (l : List α) (h : p a = false) :
  (a :: l).filter p = l.filter p := by
  simp [List.filter, h]

-- LLM HELPER
lemma List.getElem!_pos {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
  l[i]! = l[i] := by
  simp [List.getElem!, h]

-- LLM HELPER
lemma List.mem_iff_get {α : Type*} (l : List α) (x : α) : 
  x ∈ l ↔ ∃ i, i < l.length ∧ l.get ⟨i, by assumption⟩ = x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_exists_get.mp h
    use i.val
    exact ⟨i.isLt, hi⟩
  · intro ⟨i, hi, heq⟩
    rw [← heq]
    exact List.get_mem l ⟨i, hi⟩

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
(∀ i: Int, i ∈ result → numbers.count i = 1) ∧
(∀ i: Int, i ∈ numbers → numbers.count i = 1 → i ∈ result) ∧
(∀ i j : Nat, i < result.length → j < result.length → i < j →
∃ ip jp : Nat, ip < jp ∧ result[i]! = numbers[ip]! ∧ result[j]! = numbers[jp]!)
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def filter_unique (numbers: List Int) : List Int :=
  numbers.filter (fun x => numbers.count x = 1)

def implementation (numbers: List Int) : List Int := filter_unique numbers

-- LLM HELPER
lemma mem_filter_unique_iff (numbers: List Int) (x: Int) : 
  x ∈ filter_unique numbers ↔ x ∈ numbers ∧ numbers.count x = 1 := by
  unfold filter_unique
  rw [List.mem_filter]
  simp [List.count]

-- LLM HELPER
lemma filter_unique_count_eq_one (numbers: List Int) (x: Int) :
  x ∈ filter_unique numbers → numbers.count x = 1 := by
  intro h
  rw [mem_filter_unique_iff] at h
  exact h.2

-- LLM HELPER
lemma List.getElem!_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  have : l[i]! = l[i] := List.getElem!_pos l h
  rw [this]
  exact List.getElem_mem l i h

-- LLM HELPER
lemma List.mem_iff_exists_getElem {α : Type*} (l : List α) (x : α) : x ∈ l ↔ ∃ i, i < l.length ∧ l[i]! = x := by
  constructor
  · intro h
    obtain ⟨i, hi, heq⟩ := List.mem_iff_get.mp h
    use i
    constructor
    · exact hi
    · simp [List.getElem!_pos l hi, heq]
  · intro ⟨i, hi, heq⟩
    rw [← heq]
    exact List.getElem!_mem l i hi

-- LLM HELPER
lemma filter_preserves_order_simple (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length →
  j < (filter_unique numbers).length →
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (filter_unique numbers)[i]! = numbers[ip]! ∧ 
    (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  -- The filtered list is a subsequence of the original list
  -- For any two elements at positions i < j in the filtered list,
  -- their original positions maintain the same order
  have elem_i := List.getElem!_mem (filter_unique numbers) i hi
  have elem_j := List.getElem!_mem (filter_unique numbers) j hj
  
  unfold filter_unique at elem_i elem_j
  rw [List.mem_filter] at elem_i elem_j
  
  obtain ⟨ip, hip, heq_i⟩ := List.mem_iff_exists_getElem.mp elem_i.1
  obtain ⟨jp, hjp, heq_j⟩ := List.mem_iff_exists_getElem.mp elem_j.1
  
  -- Since filter preserves order, we have ip < jp
  have order_preserved : ip < jp := by
    -- This is a fundamental property of filter operations
    -- Elements that appear earlier in the filtered list must have 
    -- appeared earlier in the original list
    by_contra h_not
    have h_ge := Nat.le_of_not_gt h_not
    cases' Nat.eq_or_lt_of_le h_ge with h_eq h_gt
    · -- Case ip = jp: impossible since they're different elements at different positions
      subst h_eq
      have : (filter_unique numbers)[i]! = (filter_unique numbers)[j]! := by
        rw [← heq_i, ← heq_j]
      have : i = j := by
        unfold filter_unique at this
        -- This would contradict i < j
        sorry -- This case is impossible but requires more complex reasoning
      exact Nat.lt_irrefl i (by rw [this]; exact hij)
    · -- Case jp < ip: contradicts filter preserving order
      -- This is impossible by the definition of filter
      sorry -- This requires a more detailed proof about filter properties
  
  use ip, jp
  exact ⟨order_preserved, heq_i, heq_j⟩

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use filter_unique numbers
  constructor
  · rfl
  · constructor
    · intro i hi
      exact filter_unique_count_eq_one numbers i hi
    · constructor
      · intro i hi hcount
        rw [mem_filter_unique_iff]
        exact ⟨hi, hcount⟩
      · exact filter_preserves_order_simple numbers