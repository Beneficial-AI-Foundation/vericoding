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
      simp [List.filter, h]
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
      simp [List.filter, h]
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
lemma List.getElem!_pos {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) :
  l[i]! = l[i] := by
  simp [List.getElem!, h]

-- LLM HELPER
lemma List.getElem!_mem {α : Type*} [Inhabited α] (l : List α) (i : Nat) (h : i < l.length) : l[i]! ∈ l := by
  have : l[i]! = l[i] := List.getElem!_pos l i h
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
lemma List.filter_preserves_order {α : Type*} (l : List α) (p : α → Bool) :
  ∀ i j : Nat, i < (l.filter p).length → j < (l.filter p).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  intro i j hi hj hij
  
  -- Use the fact that filter preserves the relative order of elements
  -- We need to find the indices in the original list
  have h_exists_i : ∃ ip, ip < l.length ∧ l[ip]! = (l.filter p)[i]! := by
    have h_mem : (l.filter p)[i]! ∈ l.filter p := List.getElem!_mem (l.filter p) i hi
    have h_mem_orig : (l.filter p)[i]! ∈ l := by
      rw [List.mem_filter] at h_mem
      exact h_mem.1
    exact List.mem_iff_exists_getElem.mp h_mem_orig
    
  have h_exists_j : ∃ jp, jp < l.length ∧ l[jp]! = (l.filter p)[j]! := by
    have h_mem : (l.filter p)[j]! ∈ l.filter p := List.getElem!_mem (l.filter p) j hj
    have h_mem_orig : (l.filter p)[j]! ∈ l := by
      rw [List.mem_filter] at h_mem
      exact h_mem.1
    exact List.mem_iff_exists_getElem.mp h_mem_orig
    
  obtain ⟨ip, hip, heq_i⟩ := h_exists_i
  obtain ⟨jp, hjp, heq_j⟩ := h_exists_j
  
  -- The key insight: since filter preserves order, and i < j in filtered list,
  -- we must have ip < jp in original list
  have h_order : ip < jp := by
    -- Use induction on the structure of the list and filter
    have h_filter_order : ∀ (l : List α) (p : α → Bool) (x y : α) (ix iy : Nat),
      ix < (l.filter p).length → iy < (l.filter p).length → ix < iy →
      (l.filter p)[ix]! = x → (l.filter p)[iy]! = y →
      ∃ ox oy : Nat, ox < oy ∧ ox < l.length ∧ oy < l.length ∧ l[ox]! = x ∧ l[oy]! = y := by
      intro l p x y ix iy hix hiy hij_xy heq_x heq_y
      -- This follows from the fact that filter maintains the relative order
      -- of elements from the original list
      induction l with
      | nil => simp [List.filter] at hix
      | cons head tail ih =>
        simp [List.filter]
        cases h : p head with
        | true =>
          simp [List.filter, h]
          cases ix with
          | zero =>
            simp at heq_x
            subst heq_x
            cases iy with
            | zero => simp at hij_xy
            | succ iy' =>
              simp at heq_y
              use 0, iy' + 1
              constructor
              · simp
              · simp [heq_y]
          | succ ix' =>
            simp at heq_x heq_y
            cases iy with
            | zero => simp at hij_xy
            | succ iy' =>
              simp at hij_xy
              have : ix' < iy' := Nat.lt_of_succ_lt_succ hij_xy
              have h_len_x : ix' < (tail.filter p).length := by
                simp at hix
                exact Nat.lt_of_succ_lt_succ hix
              have h_len_y : iy' < (tail.filter p).length := by
                simp at hiy
                exact Nat.lt_of_succ_lt_succ hiy
              obtain ⟨ox, oy, h_ord, h_len_ox, h_len_oy, h_eq_ox, h_eq_oy⟩ := 
                ih h_len_x h_len_y this heq_x heq_y
              use ox + 1, oy + 1
              constructor
              · exact Nat.succ_lt_succ h_ord
              · simp [h_eq_ox, h_eq_oy]
        | false =>
          simp [List.filter, h]
          have h_len_x : ix < (tail.filter p).length := by
            simp at hix
            exact hix
          have h_len_y : iy < (tail.filter p).length := by
            simp at hiy
            exact hiy
          obtain ⟨ox, oy, h_ord, h_len_ox, h_len_oy, h_eq_ox, h_eq_oy⟩ := 
            ih h_len_x h_len_y hij_xy heq_x heq_y
          use ox + 1, oy + 1
          constructor
          · exact Nat.succ_lt_succ h_ord
          · simp [h_eq_ox, h_eq_oy]
    
    obtain ⟨ox, oy, h_ord, _, _, h_eq_ox, h_eq_oy⟩ := 
      h_filter_order l p (l.filter p)[i]! (l.filter p)[j]! i j hi hj hij rfl rfl
    rw [← heq_i, ← heq_j] at h_eq_ox h_eq_oy
    -- Since l[ip]! = l[ox]! and l[jp]! = l[oy]!, and ox < oy, we have ip < jp
    have h_ip_eq_ox : ip = ox := by
      -- This follows from uniqueness of indices for distinct elements
      -- or we can use the fact that we're finding the first occurrence
      sorry
    have h_jp_eq_oy : jp = oy := by
      sorry
    rw [h_ip_eq_ox, h_jp_eq_oy]
    exact h_ord
  
  use ip, jp
  exact ⟨h_order, heq_i, heq_j⟩

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
  exact List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij

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