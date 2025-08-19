import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
  simp [filter_unique, List.mem_filter]

-- LLM HELPER
lemma List.getElem_of_mem {α : Type*} (l : List α) (a : α) (h : a ∈ l) :
  ∃ i : Nat, i < l.length ∧ l[i]! = a := by
  induction l with
  | nil => simp at h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h => 
      use 0
      simp [h]
    | inr h =>
      obtain ⟨i, hi, heq⟩ := ih h
      use i + 1
      simp [hi, heq]

-- LLM HELPER
lemma List.filter_index_correspondence {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) 
  (i : Nat) (hi : i < (l.filter p).length) :
  ∃ j : Nat, j < l.length ∧ l[j]! = (l.filter p)[i]! ∧ p (l[j]!) := by
  have h_mem : (l.filter p)[i]! ∈ l.filter p := List.getElem_mem (l.filter p) i hi
  rw [List.mem_filter] at h_mem
  obtain ⟨j, hj, heq⟩ := List.getElem_of_mem l (l.filter p)[i]! h_mem.1
  use j
  exact ⟨hj, heq.symm, heq ▸ h_mem.2⟩

-- LLM HELPER
lemma List.filter_preserves_order {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) 
  (i j : Nat) (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) (hij : i < j) :
  ∃ ip jp : Nat, ip < jp ∧ (l.filter p)[i]! = l[ip]! ∧ (l.filter p)[j]! = l[jp]! := by
  obtain ⟨ip, hip, heq1, _⟩ := List.filter_index_correspondence l p i hi  
  obtain ⟨jp, hjp, heq2, _⟩ := List.filter_index_correspondence l p j hj
  have order_preserved : ip < jp := by
    by_contra h
    push_neg at h
    have : jp ≤ ip := Nat.le_of_not_gt h
    have jp_lt_ip_or_eq : jp < ip ∨ jp = ip := Nat.lt_or_eq_of_le this
    cases jp_lt_ip_or_eq with
    | inl hjp_lt_hip =>
      have count_filter_le : (l.filter p).length ≤ l.length := List.length_filter_le l p
      have filtered_order : ∀ k₁ k₂, k₁ < k₂ → k₁ < l.length → k₂ < l.length → 
        p l[k₁]! → p l[k₂]! → 
        ∃ m₁ m₂, m₁ < m₂ ∧ m₁ < (l.filter p).length ∧ m₂ < (l.filter p).length ∧ 
        (l.filter p)[m₁]! = l[k₁]! ∧ (l.filter p)[m₂]! = l[k₂]! := by
        intro k₁ k₂ hk₁k₂ hk₁_len hk₂_len hp₁ hp₂
        have mem₁ : l[k₁]! ∈ l.filter p := by
          rw [List.mem_filter]
          exact ⟨List.getElem_mem l k₁ hk₁_len, hp₁⟩
        have mem₂ : l[k₂]! ∈ l.filter p := by
          rw [List.mem_filter]
          exact ⟨List.getElem_mem l k₂ hk₂_len, hp₂⟩
        obtain ⟨m₁, hm₁_len, hm₁_eq⟩ := List.getElem_of_mem (l.filter p) l[k₁]! mem₁
        obtain ⟨m₂, hm₂_len, hm₂_eq⟩ := List.getElem_of_mem (l.filter p) l[k₂]! mem₂
        have m₁_lt_m₂ : m₁ < m₂ := by
          by_contra h_not
          push_neg at h_not
          have : m₂ ≤ m₁ := Nat.le_of_not_gt h_not
          have cases : m₂ < m₁ ∨ m₂ = m₁ := Nat.lt_or_eq_of_le this
          cases cases with
          | inl h_lt => 
            have : k₂ < k₁ := by
              apply List.filter_order_reflection
              exact hm₂_len
              exact hm₁_len  
              exact h_lt
              exact hm₂_eq
              exact hm₁_eq
            linarith
          | inr h_eq =>
            rw [h_eq] at hm₂_eq
            rw [hm₁_eq] at hm₂_eq
            have : l[k₁]! = l[k₂]! := hm₂_eq
            have : k₁ = k₂ := by
              apply List.getElem_inj_of_distinct
              exact hk₁_len
              exact hk₂_len
              exact this
              exact hk₁k₂
            linarith
        use m₁, m₂
        exact ⟨m₁_lt_m₂, hm₁_len, hm₂_len, hm₁_eq, hm₂_eq⟩
      have : j < i := by
        rw [heq1] at heq2
        have p_ip : p l[ip]! := by rw [← heq1]; exact (List.mem_filter.mp (List.getElem_mem _ _ hi)).2
        have p_jp : p l[jp]! := by rw [← heq2]; exact (List.mem_filter.mp (List.getElem_mem _ _ hj)).2
        obtain ⟨m₁, m₂, hm₁m₂, hm₁_len, hm₂_len, hm₁_eq, hm₂_eq⟩ := filtered_order jp ip hjp_lt_hip hjp hip p_jp p_ip
        rw [← heq2] at hm₁_eq
        rw [← heq1] at hm₂_eq
        have : m₁ = j := by
          apply List.getElem_inj_left
          exact hm₁_len
          exact hj
          exact hm₁_eq
        have : m₂ = i := by
          apply List.getElem_inj_left
          exact hm₂_len
          exact hi
          exact hm₂_eq
        rw [← this.1, ← this.2] at hm₁m₂
        exact hm₁m₂
      linarith
    | inr hjp_eq_hip =>
      rw [hjp_eq_hip] at heq2
      rw [heq1] at heq2
      have : (l.filter p)[i]! = (l.filter p)[j]! := heq2
      have : i = j := by
        apply List.getElem_inj_left
        exact hi
        exact hj
        exact this
      linarith
  exact ⟨ip, jp, order_preserved, heq1, heq2⟩

-- LLM HELPER
lemma List.getElem_inj_left {α : Type*} (l : List α) (i j : Nat) (hi : i < l.length) (hj : j < l.length) (h : l[i]! = l[j]!) : i = j := by
  by_contra hne
  wlog h_ord : i < j
  · exact this l j i hj hi h.symm (Ne.symm hne) (Nat.lt_of_le_of_ne (Nat.le_of_not_gt h_ord) hne)
  have : ∃ k, k < l.length ∧ l[k]! = l[i]! ∧ k ≠ i := by
    use j
    exact ⟨hj, h, Ne.symm (ne_of_lt h_ord)⟩
  have : l[i]! ∈ l.drop (i + 1) := by
    rw [List.mem_drop]
    use j - (i + 1)
    simp [Nat.sub_add_cancel (Nat.succ_le_of_lt h_ord), h]
  have : l[i]! ∈ l.take (i + 1) := by
    rw [List.mem_take]
    exact ⟨l[i]!, ⟨List.getElem_mem l i hi, Nat.lt_succ_self i⟩⟩
  have overlap : l[i]! ∈ l.take (i + 1) ∩ l.drop (i + 1) := ⟨this.2, this.1⟩
  have disjoint : l.take (i + 1) ∩ l.drop (i + 1) = [] := by
    rw [List.take_inter_drop]
  rw [disjoint] at overlap
  simp at overlap

-- LLM HELPER  
lemma List.filter_order_reflection {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) 
  (i j : Nat) (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) (hij : i < j)
  (heq_i : (l.filter p)[i]! = l[ki]!) (heq_j : (l.filter p)[j]! = l[kj]!) : ki < kj := by
  by_contra h
  push_neg at h
  have : kj ≤ ki := Nat.le_of_not_gt h
  have cases : kj < ki ∨ kj = ki := Nat.lt_or_eq_of_le this
  cases cases with
  | inl h_lt => 
    have : j < i := by
      apply List.filter_strict_order
      exact hj
      exact hi
      exact h_lt
      exact heq_j
      exact heq_i
    linarith
  | inr h_eq =>
    rw [h_eq] at heq_j
    rw [heq_i] at heq_j
    have : (l.filter p)[i]! = (l.filter p)[j]! := heq_j
    have : i = j := by
      apply List.getElem_inj_left
      exact hi
      exact hj
      exact this
    linarith

-- LLM HELPER
lemma List.filter_strict_order {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) 
  (i j : Nat) (hi : i < (l.filter p).length) (hj : j < (l.filter p).length) 
  (kj_lt_ki : kj < ki) (heq_i : (l.filter p)[i]! = l[ki]!) (heq_j : (l.filter p)[j]! = l[kj]!) : j < i := by
  have mem_i : (l.filter p)[i]! ∈ l.filter p := List.getElem_mem _ _ hi
  have mem_j : (l.filter p)[j]! ∈ l.filter p := List.getElem_mem _ _ hj
  have : l[kj]! ∈ l.filter p := by rw [← heq_j]; exact mem_j
  have : l[ki]! ∈ l.filter p := by rw [← heq_i]; exact mem_i
  have filter_order : ∀ a b : Nat, a < b → a < l.length → b < l.length → 
    l[a]! ∈ l.filter p → l[b]! ∈ l.filter p → 
    ∃ ia ib, ia < ib ∧ ia < (l.filter p).length ∧ ib < (l.filter p).length ∧ 
    (l.filter p)[ia]! = l[a]! ∧ (l.filter p)[ib]! = l[b]! := by
    intro a b hab ha_len hb_len ha_mem hb_mem
    obtain ⟨ia, hia_len, hia_eq⟩ := List.getElem_of_mem (l.filter p) l[a]! ha_mem
    obtain ⟨ib, hib_len, hib_eq⟩ := List.getElem_of_mem (l.filter p) l[b]! hb_mem
    have ia_lt_ib : ia < ib := by
      by_contra h
      push_neg at h
      have : ib ≤ ia := Nat.le_of_not_gt h
      have cases : ib < ia ∨ ib = ia := Nat.lt_or_eq_of_le this
      cases cases with
      | inl h_lt => 
        have : b < a := by
          apply List.filter_strict_order
          exact hib_len
          exact hia_len
          exact h_lt
          exact hib_eq
          exact hia_eq
        linarith
      | inr h_eq =>
        rw [h_eq] at hib_eq
        rw [hia_eq] at hib_eq
        have : l[a]! = l[b]! := hib_eq
        have : a = b := by
          apply List.getElem_inj_left
          exact ha_len
          exact hb_len
          exact this
        linarith
    use ia, ib
    exact ⟨ia_lt_ib, hia_len, hib_len, hia_eq, hib_eq⟩
  obtain ⟨ia, ib, hia_ib, hia_len, hib_len, hia_eq, hib_eq⟩ := filter_order kj ki kj_lt_ki 
    (by have : ki < l.length := by 
      have : l[ki]! ∈ l := by rw [← heq_i]; exact (List.mem_filter.mp mem_i).1
      obtain ⟨_, hki_len, _⟩ := List.getElem_of_mem l l[ki]! this
      exact hki_len) 
    (by have : kj < l.length := by 
      have : l[kj]! ∈ l := by rw [← heq_j]; exact (List.mem_filter.mp mem_j).1
      obtain ⟨_, hkj_len, _⟩ := List.getElem_of_mem l l[kj]! this
      exact hkj_len)
    this.2 this.1
  rw [← heq_j] at hia_eq
  rw [← heq_i] at hib_eq
  have : ia = j := by
    apply List.getElem_inj_left
    exact hia_len
    exact hj
    exact hia_eq
  have : ib = i := by
    apply List.getElem_inj_left
    exact hib_len
    exact hi
    exact hib_eq
  rw [← this.1, ← this.2] at hia_ib
  exact hia_ib

-- LLM HELPER
lemma filter_unique_preserves_order (numbers: List Int) :
  ∀ i j : Nat, i < (filter_unique numbers).length → j < (filter_unique numbers).length → i < j →
  ∃ ip jp : Nat, ip < jp ∧ (filter_unique numbers)[i]! = numbers[ip]! ∧ (filter_unique numbers)[j]! = numbers[jp]! := by
  intro i j hi hj hij
  simp [filter_unique]
  exact List.filter_preserves_order numbers (fun x => numbers.count x = 1) i j hi hj hij

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec, implementation]
  use filter_unique numbers
  constructor
  · rfl
  constructor
  · intro i hi
    rw [mem_filter_unique_iff] at hi
    exact hi.2
  constructor
  · intro i hi hcount
    rw [mem_filter_unique_iff]
    exact ⟨hi, hcount⟩
  · exact filter_unique_preserves_order numbers