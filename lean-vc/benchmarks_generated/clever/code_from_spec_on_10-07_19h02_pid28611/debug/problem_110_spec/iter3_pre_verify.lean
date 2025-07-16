import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: List Int → List Int → String)
(lst1: List Int)
(lst2: List Int) :=
let spec (result : String) :=
  lst1 ≠ [] → lst2 ≠ [] →
  let bool_result := ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!))
  (bool_result → result = "YES") ∧
  (result = "NO" → ¬ bool_result) ∧
  (result ≠ "YES" ∧ result ≠ "NO" → False)
∃ result,
  implementation lst1 lst2 = result ∧
  spec result

def implementation (lst1: List Int) (lst2: List Int) : String :=
  if lst1.isEmpty || lst2.isEmpty then "NO"
  else
    let odd_count1 := (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i)) |>.length
    let even_count2 := (List.range lst2.length).filter (fun i => Even (lst2.get! i)) |>.length
    if odd_count1 ≤ even_count2 then "YES" else "NO"

-- LLM HELPER
lemma not_even_iff_odd (n : Int) : ¬ Even n ↔ Odd n := by
  constructor
  · intro h_not_even
    rw [Int.odd_iff_not_even]
    exact h_not_even
  · intro h_odd
    rw [Int.odd_iff_not_even] at h_odd
    exact h_odd

-- LLM HELPER
lemma List.nodup_map_fst_of_nodup {α β : Type*} (l : List (α × β)) (h : l.Nodup) : 
  (l.map (fun (a, _) => a)).Nodup := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp at h
    simp [List.map_cons, List.nodup_cons]
    constructor
    · intro h_mem
      simp [List.mem_map] at h_mem
      obtain ⟨⟨a, b⟩, h_mem_tail, h_eq⟩ := h_mem
      simp at h_eq
      rw [← h_eq]
      exact h.1 h_mem_tail
    · exact ih h.2

-- LLM HELPER
lemma List.nodup_map_snd_of_nodup {α β : Type*} (l : List (α × β)) (h : l.Nodup) : 
  (l.map (fun (_, b) => b)).Nodup := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp at h
    simp [List.map_cons, List.nodup_cons]
    constructor
    · intro h_mem
      simp [List.mem_map] at h_mem
      obtain ⟨⟨a, b⟩, h_mem_tail, h_eq⟩ := h_mem
      simp at h_eq
      rw [← h_eq]
      exact h.1 h_mem_tail
    · exact ih h.2

-- LLM HELPER
lemma exists_exchange_of_sufficient_evens (lst1 lst2 : List Int) 
  (h_ne1 : lst1 ≠ []) (h_ne2 : lst2 ≠ [])
  (h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
             ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length) :
  ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, _) => a)
    let lst2_idxs := exchange.map (fun (_, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!)) := by
  let odd_indices := (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))
  let even_indices := (List.range lst2.length).filter (fun i => Even (lst2.get! i))
  let exchange := (odd_indices.zip even_indices).take (min odd_indices.length even_indices.length)
  use exchange
  let lst1_idxs := exchange.map (fun (a, _) => a)
  let lst2_idxs := exchange.map (fun (_, b) => b)
  constructor
  · simp [List.all_eq_true, lst1_idxs]
    intro i h_mem
    simp [List.mem_map] at h_mem
    obtain ⟨⟨i', j⟩, h_pair_mem, h_eq⟩ := h_mem
    simp at h_eq
    rw [← h_eq]
    simp [List.mem_take, List.mem_zip] at h_pair_mem
    have h_mem_odd : i' ∈ odd_indices := h_pair_mem.1.1
    simp [List.mem_filter, List.mem_range] at h_mem_odd
    exact h_mem_odd.1
  constructor
  · simp [List.all_eq_true, lst2_idxs]
    intro j h_mem
    simp [List.mem_map] at h_mem
    obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := h_mem
    simp at h_eq
    rw [← h_eq]
    simp [List.mem_take, List.mem_zip] at h_pair_mem
    have h_mem_even : j' ∈ even_indices := h_pair_mem.1.2
    simp [List.mem_filter, List.mem_range] at h_mem_even
    exact h_mem_even.1
  constructor
  · apply List.nodup_map_fst_of_nodup
    apply List.Nodup.take
    apply List.nodup_zip_of_nodup_left
    apply List.nodup_filter
    exact List.nodup_range _
  constructor
  · apply List.nodup_map_snd_of_nodup
    apply List.Nodup.take
    apply List.nodup_zip_of_nodup_right
    apply List.nodup_filter
    exact List.nodup_range _
  · intro i h_i_lt
    constructor
    · intro h_not_mem
      by_contra h_not_even
      have h_odd : Odd (lst1.get! i) := not_even_iff_odd (lst1.get! i) |>.mp h_not_even
      have h_mem_odd : i ∈ odd_indices := by
        simp [List.mem_filter, List.mem_range]
        exact ⟨h_i_lt, h_not_even⟩
      have h_mem_lst1_idxs : i ∈ lst1_idxs := by
        simp [lst1_idxs, List.mem_map]
        have h_exists_pair : ∃ j, (i, j) ∈ exchange := by
          simp [List.mem_take, List.mem_zip]
          constructor
          · exact ⟨h_mem_odd, by simp [even_indices]⟩
          · simp [min_le_iff]
            left
            apply List.mem_iff_get.mp at h_mem_odd
            obtain ⟨k, h_k_bound, h_get_k⟩ := h_mem_odd
            have h_k_lt : k < min odd_indices.length even_indices.length := by
              simp [min_le_iff]
              left
              exact h_k_bound
            exact k < min odd_indices.length even_indices.length
        obtain ⟨j, h_pair_mem⟩ := h_exists_pair
        use (i, j)
        exact ⟨h_pair_mem, rfl⟩
      exact h_not_mem h_mem_lst1_idxs
    · intro h_mem
      simp [lst1_idxs, List.mem_map] at h_mem
      obtain ⟨⟨i', j⟩, h_pair_mem, h_eq⟩ := h_mem
      simp at h_eq
      rw [← h_eq]
      simp [List.mem_take, List.mem_zip] at h_pair_mem
      have h_mem_even : j ∈ even_indices := h_pair_mem.1.2
      simp [List.mem_filter, List.mem_range] at h_mem_even
      exact h_mem_even.2

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h_ne1 h_ne2
    simp [implementation]
    constructor
    · intro h_bool
      simp only [if_neg (not_or_of_not (List.not_isEmpty_iff.mpr h_ne1) (List.not_isEmpty_iff.mpr h_ne2))]
      obtain ⟨exchange, h_prop⟩ := h_bool
      let lst1_idxs := exchange.map (fun (a, _) => a)
      let lst2_idxs := exchange.map (fun (_, b) => b)
      have h_all_odd_in_idxs : ∀ i, i < lst1.length → ¬ Even (lst1.get! i) → i ∈ lst1_idxs := by
        intro i h_i_lt h_not_even
        by_contra h_not_mem
        have h_even := (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
        exact h_not_even h_even
      have h_odd_subset : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).toFinset ⊆ lst1_idxs.toFinset := by
        intro i h_mem
        simp [List.mem_toFinset, List.mem_filter, List.mem_range] at h_mem
        simp [List.mem_toFinset]
        exact h_all_odd_in_idxs i h_mem.1 h_mem.2
      have h_card_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
        rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
        rw [← List.toFinset_card_of_nodup h_prop.2.2.1]
        exact Finset.card_le_card h_odd_subset
      have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
        simp [lst1_idxs, lst2_idxs, List.length_map]
      rw [h_equal_len] at h_card_le
      have h_even_bound : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
        rw [← List.toFinset_card_of_nodup h_prop.2.2.2.1]
        rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
        apply Finset.card_le_card
        intro j h_mem
        simp [List.mem_toFinset] at h_mem ⊢
        simp [List.mem_filter, List.mem_range]
        have h_valid : j < lst2.length := by
          simp [List.all_eq_true] at h_prop
          exact h_prop.2.1 j h_mem
        constructor
        · exact h_valid
        · have h_exists_i : ∃ i, i ∈ lst1_idxs ∧ lst2_idxs.get! (lst1_idxs.indexesOf i).head! = j := by
            simp [lst2_idxs, List.mem_map] at h_mem
            obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := h_mem
            simp at h_eq
            rw [← h_eq]
            use i
            constructor
            · simp [lst1_idxs, List.mem_map]
              use (i, j')
              exact ⟨h_pair_mem, rfl⟩
            · simp [lst1_idxs, lst2_idxs, List.get!_eq_get]
              congr
          obtain ⟨i, h_i_mem, h_j_eq⟩ := h_exists_i
          have h_i_lt : i < lst1.length := by
            simp [List.all_eq_true] at h_prop
            exact h_prop.1 i h_i_mem
          have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
            exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
          rw [← h_j_eq] at h_even_j
          exact h_even_j
      exact le_trans h_card_le h_even_bound
    · constructor
      · intro h_no
        simp only [if_neg (not_or_of_not (List.not_isEmpty_iff.mpr h_ne1) (List.not_isEmpty_iff.mpr h_ne2))] at h_no
        simp only [if_neg] at h_no
        by_contra h_bool
        have h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                       ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
          obtain ⟨exchange, h_prop⟩ := h_bool
          let lst1_idxs := exchange.map (fun (a, _) => a)
          let lst2_idxs := exchange.map (fun (_, b) => b)
          have h_all_odd_in_idxs : ∀ i, i < lst1.length → ¬ Even (lst1.get! i) → i ∈ lst1_idxs := by
            intro i h_i_lt h_not_even
            by_contra h_not_mem
            have h_even := (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
            exact h_not_even h_even
          have h_odd_subset : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).toFinset ⊆ lst1_idxs.toFinset := by
            intro i h_mem
            simp [List.mem_toFinset, List.mem_filter, List.mem_range] at h_mem
            simp [List.mem_toFinset]
            exact h_all_odd_in_idxs i h_mem.1 h_mem.2
          have h_card_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
            rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
            rw [← List.toFinset_card_of_nodup h_prop.2.2.1]
            exact Finset.card_le_card h_odd_subset
          have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
            simp [lst1_idxs, lst2_idxs, List.length_map]
          rw [h_equal_len] at h_card_le
          have h_even_bound : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
            rw [← List.toFinset_card_of_nodup h_prop.2.2.2.1]
            rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
            apply Finset.card_le_card
            intro j h_mem
            simp [List.mem_toFinset] at h_mem ⊢
            simp [List.mem_filter, List.mem_range]
            have h_valid : j < lst2.length := by
              simp [List.all_eq_true] at h_prop
              exact h_prop.2.1 j h_mem
            constructor
            · exact h_valid
            · have h_exists_i : ∃ i, i ∈ lst1_idxs ∧ lst2_idxs.get! (lst1_idxs.indexesOf i).head! = j := by
                simp [lst2_idxs, List.mem_map] at h_mem
                obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := h_mem
                simp at h_eq
                rw [← h_eq]
                use i
                constructor
                · simp [lst1_idxs, List.mem_map]
                  use (i, j')
                  exact ⟨h_pair_mem, rfl⟩
                · simp [lst1_idxs, lst2_idxs, List.get!_eq_get]
                  congr
              obtain ⟨i, h_i_mem, h_j_eq⟩ := h_exists_i
              have h_i_lt : i < lst1.length := by
                simp [List.all_eq_true] at h_prop
                exact h_prop.1 i h_i_mem
              have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
              rw [← h_j_eq] at h_even_j
              exact h_even_j
          exact le_trans h_card_le h_even_bound
        contradiction
      · intro h_neither
        simp only [if_neg (not_or_of_not (List.not_isEmpty_iff.mpr h_ne1) (List.not_isEmpty_iff.mpr h_ne2))] at h_neither
        by_cases h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                           ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length
        · simp only [if_pos h_count] at h_neither
          exact h_neither.1 rfl
        · simp only [if_neg h_count] at h_neither
          exact h_neither.2 rfl