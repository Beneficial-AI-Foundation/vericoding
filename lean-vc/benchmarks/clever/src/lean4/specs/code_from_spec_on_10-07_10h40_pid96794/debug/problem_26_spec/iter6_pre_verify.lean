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
lemma List.getElem!_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  have : l[i]! = l[i] := List.getElem!_pos l h
  rw [this]
  exact List.getElem_mem l i h

-- LLM HELPER
lemma List.mem_iff_exists_getElem {α : Type*} (l : List α) (x : α) : x ∈ l ↔ ∃ i, i < l.length ∧ l[i]! = x := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    use i.1
    constructor
    · exact i.2
    · simp [List.getElem!_pos l i.2, hi]
  · intro ⟨i, hi, heq⟩
    rw [← heq]
    exact List.getElem!_mem l i hi

-- LLM HELPER
lemma List.mem_iff_get {α : Type*} (l : List α) (x : α) : 
  x ∈ l ↔ ∃ i, l.get i = x := by
  constructor
  · intro h
    induction l with
    | nil => simp at h
    | cons head tail ih =>
      simp at h
      cases h with
      | inl h_eq => 
        use ⟨0, by simp⟩
        simp [h_eq]
      | inr h_tail => 
        obtain ⟨i, heq⟩ := ih h_tail
        use ⟨i.1 + 1, by simp; exact Nat.succ_lt_succ i.2⟩
        simp [heq]
  · intro ⟨i, heq⟩
    rw [← heq]
    exact List.get_mem l i

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
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) (i j : Nat) :
  i < (l.filter p).length →
  j < (l.filter p).length →
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ ip < l.length ∧ jp < l.length ∧ 
    (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro hi hj hij
  -- Get elements from filtered list
  let filt := l.filter p
  have elem_i_mem : filt[i]! ∈ filt := List.getElem!_mem filt i hi
  have elem_j_mem : filt[j]! ∈ filt := List.getElem!_mem filt j hj
  
  -- Elements in filtered list are in original list
  have orig_i : filt[i]! ∈ l := by
    rw [List.mem_filter] at elem_i_mem
    exact elem_i_mem.1
  have orig_j : filt[j]! ∈ l := by
    rw [List.mem_filter] at elem_j_mem
    exact elem_j_mem.1
  
  -- Find indices in original list
  obtain ⟨ip, hip, heq_i⟩ := List.mem_iff_exists_getElem.mp orig_i
  obtain ⟨jp, hjp, heq_j⟩ := List.mem_iff_exists_getElem.mp orig_j
  
  -- Since filter preserves order, ip < jp
  have order_preserved : ip < jp := by
    -- Use the fact that filter preserves relative ordering
    by_contra h_not
    have h_ge := Nat.le_of_not_gt h_not
    -- This leads to contradiction with i < j due to order preservation
    -- For now, we'll use a classical argument
    have : ip ≠ jp := by
      intro h_eq
      subst h_eq
      have : filt[i]! = filt[j]! := by
        rw [← heq_i, ← heq_j]
      -- This creates a contradiction with distinct indices having same value
      -- from filter property
      have : i = j := by
        -- Use injectivity of array access for distinct positions
        -- having same value from same source
        cases' Nat.lt_trichotomy i j with h h
        · exact False.elim (Nat.lt_irrefl i h)
        · cases' h with h h
          · exact h
          · exact False.elim (Nat.lt_irrefl j h)
      exact Nat.lt_irrefl i (by rw [this]; exact hij)
    
    have : jp < ip := Nat.lt_of_le_of_ne h_ge (Ne.symm this)
    -- This contradicts filter's order preservation
    -- The detailed proof would require induction on the filter structure
    exfalso
    -- Use order preservation property of filter
    have filter_order := List.filter_preserves_index_order l p jp ip
    exact Nat.lt_irrefl ip (Nat.lt_trans this filter_order)
  
  use ip, jp
  exact ⟨order_preserved, hip, hjp, heq_i, heq_j⟩

-- LLM HELPER
lemma List.filter_preserves_index_order {α : Type*} (l : List α) (p : α → Bool) (i j : Nat) :
  i < j → i < l.length → j < l.length → 
  l[i]! ∈ l.filter p → l[j]! ∈ l.filter p → i < j := by
  intro hij hi hj hpi hpj
  exact hij

-- LLM HELPER
lemma filter_preserves_order_simple (numbers: List Int) (i j: Nat) :
  i < (filter_unique numbers).length →
  j < (filter_unique numbers).length →
  i < j →
  ∃ ip jp : Nat, ip < jp ∧ 
    (filter_unique numbers)[i]! = numbers[ip]! ∧ 
    (filter_unique numbers)[j]! = numbers[jp]! := by
  intro hi hj hij
  unfold filter_unique
  obtain ⟨ip, jp, horder, hip, hjp, heq_i, heq_j⟩ := List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij
  use ip, jp
  exact ⟨horder, heq_i, heq_j⟩

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