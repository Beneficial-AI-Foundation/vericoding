import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Counts the number of non-zero values in a vector.
    
    The word "non-zero" is in reference to the Python 2.x
    built-in method `__nonzero__()` (renamed `__bool__()`
    in Python 3.x) of Python objects that tests an object's
    "truthfulness". For example, any number is considered
    truthful if it is nonzero, whereas any string is considered
    truthful if it is not the empty string. Thus, this function
    counts how many elements in the vector are non-zero. -/
def count_nonzero {n : Nat} (a : Vector Int n) : Id Nat :=
  a.toList.filter (· ≠ 0) |>.length

-- LLM HELPER
lemma filter_length_le_list_length {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length ≤ l.length := by
  induction l with
  | nil => simp
  | cons h t ih => 
    simp [List.filter]
    split
    · simp; exact Nat.succ_le_succ ih
    · exact Nat.le_succ_of_le ih

-- LLM HELPER
lemma vector_toList_length {α : Type*} {n : Nat} (v : Vector α n) :
    v.toList.length = n :=
  v.2

-- LLM HELPER  
lemma filter_all_false {α : Type*} (l : List α) (p : α → Bool) :
    (∀ x ∈ l, ¬p x) → (l.filter p).length = 0 := by
  intro h
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [List.filter]
    have h1 : ¬p head := h head (List.mem_cons_self head tail)
    have h2 : ∀ x ∈ tail, ¬p x := fun x hx => h x (List.mem_cons_of_mem head hx)
    simp [h1, ih h2]

-- LLM HELPER
lemma filter_all_true {α : Type*} (l : List α) (p : α → Bool) :
    (∀ x ∈ l, p x) → (l.filter p).length = l.length := by
  intro h
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [List.filter]
    have h1 : p head := h head (List.mem_cons_self head tail)
    have h2 : ∀ x ∈ tail, p x := fun x hx => h x (List.mem_cons_of_mem head hx)
    simp [h1, ih h2]

-- LLM HELPER
lemma filter_exists_true {α : Type*} (l : List α) (p : α → Bool) :
    (∃ x ∈ l, p x) → (l.filter p).length > 0 := by
  intro ⟨x, hx_mem, hx_prop⟩
  have : x ∈ l.filter p := List.mem_filter.mpr ⟨hx_mem, hx_prop⟩
  exact List.length_pos_of_mem this

-- LLM HELPER
lemma filter_exists_false {α : Type*} (l : List α) (p : α → Bool) :
    (∃ x ∈ l, ¬p x) → (l.filter p).length < l.length := by
  intro ⟨x, hx_mem, hx_prop⟩
  have h1 : x ∉ l.filter p := fun h => hx_prop (List.mem_filter.mp h).2
  have h2 : (l.filter p).length ≤ l.length := filter_length_le_list_length l p
  cases' Nat.lt_or_eq_of_le h2 with h h
  · exact h
  · exfalso
    have h3 : l.filter p = l := List.eq_filter_of_length_eq_length h
    rw [← h3] at hx_mem
    have h4 : x ∈ l.filter p := hx_mem
    exact h1 h4

-- LLM HELPER
lemma vector_get_mem_toList {α : Type*} {n : Nat} (v : Vector α n) (i : Fin n) :
    v.get i ∈ v.toList := by
  rw [Vector.get_eq_get]
  exact List.get_mem v.toList i (by rw [vector_toList_length]; exact i.2)

-- LLM HELPER
lemma List.eq_filter_of_length_eq_length {α : Type*} (l : List α) (p : α → Bool) :
    (l.filter p).length = l.length → l.filter p = l := by
  intro h
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp [List.filter]
    split
    · simp at h
      have h1 : (tail.filter p).length = tail.length := Nat.succ_inj'.mp h
      rw [ih h1]
    · simp at h
      have h2 : (tail.filter p).length = tail.length + 1 := h
      have h3 : (tail.filter p).length ≤ tail.length := filter_length_le_list_length tail p
      have : tail.length + 1 ≤ tail.length := by rw [← h2]; exact h3
      have : False := Nat.not_succ_le_self tail.length this
      exact False.elim this

/-- Specification: count_nonzero returns the number of non-zero elements in the vector.
    
    The function counts exactly those elements that are not equal to zero.
    The result is always between 0 and n (inclusive), where n is the length of the vector.
    If all elements are zero, the result is 0.
    If all elements are non-zero, the result is n. -/
theorem count_nonzero_spec {n : Nat} (a : Vector Int n) :
    ⦃⌜True⌝⦄
    count_nonzero a
    ⦃⇓count => ⌜count ≤ n ∧ 
                (n = 0 → count = 0) ∧
                ((∀ i : Fin n, a.get i = 0) → count = 0) ∧
                ((∀ i : Fin n, a.get i ≠ 0) → count = n) ∧
                ((∃ i : Fin n, a.get i ≠ 0) → count > 0) ∧
                ((∃ i : Fin n, a.get i = 0) → count < n)⌝⦄ := by
  simp [count_nonzero]
  constructor
  · rw [← vector_toList_length a]
    exact filter_length_le_list_length a.toList (· ≠ 0)
  constructor
  · intro h
    rw [h]
    simp [Vector.toList]
  constructor
  · intro h
    apply filter_all_false
    intro x hx
    simp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    rw [← vector_toList_length a] at hi
    have : x = a.get ⟨i, hi⟩ := by
      rw [Vector.get_eq_get, ← hi]
    rw [this]
    exact h ⟨i, hi⟩
  constructor
  · intro h
    rw [← vector_toList_length a]
    apply filter_all_true
    intro x hx
    simp
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hx
    rw [← vector_toList_length a] at hi
    have : x = a.get ⟨i, hi⟩ := by
      rw [Vector.get_eq_get, ← hi]
    rw [this]
    exact h ⟨i, hi⟩
  constructor
  · intro ⟨i, hi⟩
    apply filter_exists_true
    use a.get i
    constructor
    · exact vector_get_mem_toList a i
    · simp [hi]
  · intro ⟨i, hi⟩
    rw [← vector_toList_length a]
    apply filter_exists_false
    use a.get i
    constructor
    · exact vector_get_mem_toList a i
    · simp [hi]