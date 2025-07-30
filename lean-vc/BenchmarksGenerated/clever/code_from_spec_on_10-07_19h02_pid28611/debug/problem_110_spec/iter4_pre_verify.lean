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
  rw [Int.not_even_iff_odd]

-- LLM HELPER
lemma List.nodup_map_fst_of_nodup {α β : Type*} (l : List (α × β)) (h : l.Nodup) : 
  (l.map (fun (a, _) => a)).Nodup := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp at h
    cases' head with a b
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro h_mem
      simp [List.mem_map] at h_mem
      obtain ⟨⟨a', b'⟩, h_mem_tail, h_eq⟩ := h_mem
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
    cases' head with a b
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro h_mem
      simp [List.mem_map] at h_mem
      obtain ⟨⟨a', b'⟩, h_mem_tail, h_eq⟩ := h_mem
      simp at h_eq
      rw [← h_eq]
      exact h.1 h_mem_tail
    · exact ih h.2

-- LLM HELPER
lemma List.mem_zip_iff {α β : Type*} (l1 : List α) (l2 : List β) (a : α) (b : β) :
  (a, b) ∈ l1.zip l2 ↔ ∃ n, n < l1.length ∧ n < l2.length ∧ l1.get! n = a ∧ l2.get! n = b := by
  simp [List.mem_zip]

-- LLM HELPER
lemma List.mem_map_iff {α β : Type*} (f : α → β) (l : List α) (b : β) :
  b ∈ l.map f ↔ ∃ a, a ∈ l ∧ f a = b := by
  simp [List.mem_map]

-- LLM HELPER
lemma List.nodup_zip_of_nodup_left {α β : Type*} (l1 : List α) (l2 : List β) (h : l1.Nodup) :
  (l1.zip l2).Nodup := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons head tail ih =>
    cases l2 with
    | nil => simp
    | cons head2 tail2 =>
      simp at h
      rw [List.zip_cons_cons, List.nodup_cons]
      constructor
      · intro h_mem
        simp [List.mem_zip] at h_mem
        obtain ⟨n, h_n_lt, h_get⟩ := h_mem
        simp at h_get
        exact h.1 h_get.1
      · exact ih h.2

-- LLM HELPER
lemma List.nodup_zip_of_nodup_right {α β : Type*} (l1 : List α) (l2 : List β) (h : l2.Nodup) :
  (l1.zip l2).Nodup := by
  induction l2 generalizing l1 with
  | nil => simp
  | cons head tail ih =>
    cases l1 with
    | nil => simp
    | cons head1 tail1 =>
      simp at h
      rw [List.zip_cons_cons, List.nodup_cons]
      constructor
      · intro h_mem
        simp [List.mem_zip] at h_mem
        obtain ⟨n, h_n_lt, h_get⟩ := h_mem
        simp at h_get
        exact h.1 h_get.2
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [List.all_eq_true]
    intro i h_mem
    obtain ⟨⟨i', j⟩, h_pair_mem, h_eq⟩ := List.mem_map_iff.mp h_mem
    simp at h_eq
    rw [← h_eq]
    have h_in_take : (i', j) ∈ exchange := h_pair_mem
    rw [List.mem_take] at h_in_take
    have h_in_zip : (i', j) ∈ odd_indices.zip even_indices := h_in_take.1
    rw [List.mem_zip] at h_in_zip
    obtain ⟨n, h_n_lt1, h_n_lt2, h_get1, h_get2⟩ := h_in_zip
    have h_mem_odd : i' ∈ odd_indices := by
      rw [← h_get1, List.get!_eq_get]
      exact List.get_mem _ _ _
    rw [List.mem_filter, List.mem_range] at h_mem_odd
    exact h_mem_odd.1
  · rw [List.all_eq_true]
    intro j h_mem
    obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := List.mem_map_iff.mp h_mem
    simp at h_eq
    rw [← h_eq]
    have h_in_take : (i, j') ∈ exchange := h_pair_mem
    rw [List.mem_take] at h_in_take
    have h_in_zip : (i, j') ∈ odd_indices.zip even_indices := h_in_take.1
    rw [List.mem_zip] at h_in_zip
    obtain ⟨n, h_n_lt1, h_n_lt2, h_get1, h_get2⟩ := h_in_zip
    have h_mem_even : j' ∈ even_indices := by
      rw [← h_get2, List.get!_eq_get]
      exact List.get_mem _ _ _
    rw [List.mem_filter, List.mem_range] at h_mem_even
    exact h_mem_even.1
  · apply List.nodup_map_fst_of_nodup
    apply List.Nodup.take
    apply List.nodup_zip_of_nodup_left
    apply List.nodup_filter
    exact List.nodup_range _
  · apply List.nodup_map_snd_of_nodup
    apply List.Nodup.take
    apply List.nodup_zip_of_nodup_right
    apply List.nodup_filter
    exact List.nodup_range _
  · intro i h_i_lt
    constructor
    · intro h_not_mem
      by_contra h_not_even
      have h_mem_odd : i ∈ odd_indices := by
        rw [List.mem_filter, List.mem_range]
        exact ⟨h_i_lt, h_not_even⟩
      have h_exists_j : ∃ j, (i, j) ∈ exchange := by
        simp only [List.mem_take, List.mem_zip]
        refine ⟨?_, ?_⟩
        · obtain ⟨n, h_n_lt, h_get⟩ := List.mem_iff_get.mp h_mem_odd
          have h_n_lt_even : n < even_indices.length := by
            rw [← List.length_filter]
            calc n 
              _ < odd_indices.length := h_n_lt
              _ = (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i)) |>.length := by rfl
              _ ≤ (List.range lst2.length).filter (fun i => Even (lst2.get! i)) |>.length := h_count
              _ = even_indices.length := by rfl
          use n
          exact ⟨h_n_lt, h_n_lt_even, h_get, rfl⟩
        · simp only [min_le_iff]
          left
          exact List.mem_iff_get.mp h_mem_odd |>.1
      obtain ⟨j, h_pair_mem⟩ := h_exists_j
      have h_mem_lst1_idxs : i ∈ lst1_idxs := by
        rw [List.mem_map]
        use (i, j)
        exact ⟨h_pair_mem, rfl⟩
      exact h_not_mem h_mem_lst1_idxs
    · intro h_mem
      obtain ⟨⟨i', j⟩, h_pair_mem, h_eq⟩ := List.mem_map_iff.mp h_mem
      simp at h_eq
      rw [← h_eq] at h_mem
      have h_in_take : (i, j) ∈ exchange := h_pair_mem
      rw [List.mem_take] at h_in_take
      have h_in_zip : (i, j) ∈ odd_indices.zip even_indices := h_in_take.1
      rw [List.mem_zip] at h_in_zip
      obtain ⟨n, h_n_lt1, h_n_lt2, h_get1, h_get2⟩ := h_in_zip
      have h_mem_even : j ∈ even_indices := by
        rw [← h_get2, List.get!_eq_get]
        exact List.get_mem _ _ _
      rw [List.mem_filter, List.mem_range] at h_mem_even
      exact h_mem_even.2

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h_ne1 h_ne2
    rw [implementation]
    rw [if_neg]
    · constructor
      · intro h_bool
        obtain ⟨exchange, h_prop⟩ := h_bool
        let lst1_idxs := exchange.map (fun (a, _) => a)
        let lst2_idxs := exchange.map (fun (_, b) => b)
        have h_all_odd_in_idxs : ∀ i, i < lst1.length → ¬ Even (lst1.get! i) → i ∈ lst1_idxs := by
          intro i h_i_lt h_not_even
          by_contra h_not_mem
          have h_even := (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
          exact h_not_even h_even
        have h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                       ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
          have h_odd_subset : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).toFinset ⊆ lst1_idxs.toFinset := by
            intro i h_mem
            rw [List.mem_toFinset] at h_mem ⊢
            rw [List.mem_filter, List.mem_range] at h_mem
            exact h_all_odd_in_idxs i h_mem.1 h_mem.2
          have h_card_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
            rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
            rw [← List.toFinset_card_of_nodup h_prop.2.2.1]
            exact Finset.card_le_card h_odd_subset
          have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
            simp only [lst1_idxs, lst2_idxs, List.length_map]
          rw [h_equal_len] at h_card_le
          have h_even_bound : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
            rw [← List.toFinset_card_of_nodup h_prop.2.2.2.1]
            rw [← List.toFinset_card_of_nodup (List.nodup_filter _ (List.nodup_range _))]
            apply Finset.card_le_card
            intro j h_mem
            rw [List.mem_toFinset] at h_mem ⊢
            rw [List.mem_filter, List.mem_range]
            have h_valid : j < lst2.length := by
              rw [List.all_eq_true] at h_prop
              exact h_prop.2.1 j h_mem
            constructor
            · exact h_valid
            · have h_exists_i : ∃ i, i ∈ lst1_idxs ∧ ∃ idx, idx < lst1_idxs.length ∧ lst1_idxs.get! idx = i ∧ lst2_idxs.get! idx = j := by
                obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := List.mem_map_iff.mp h_mem
                simp at h_eq
                rw [← h_eq]
                use i
                constructor
                · rw [List.mem_map]
                  use (i, j')
                  exact ⟨h_pair_mem, rfl⟩
                · obtain ⟨idx, h_idx_lt, h_get⟩ := List.mem_iff_get.mp h_pair_mem
                  use idx
                  constructor
                  · rw [List.length_map]
                    exact h_idx_lt
                  · simp only [List.get!_eq_get]
                    cases' (exchange.get ⟨idx, h_idx_lt⟩) with i' j''
                    simp at h_get
                    simp only [List.get_map]
                    exact ⟨h_get.1, h_get.2⟩
              obtain ⟨i, h_i_mem, idx, h_idx_lt, h_get_i, h_get_j⟩ := h_exists_i
              have h_i_lt : i < lst1.length := by
                rw [List.all_eq_true] at h_prop
                exact h_prop.1 i h_i_mem
              have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
              rw [← h_get_j] at h_even_j
              exact h_even_j
          exact le_trans h_card_le h_even_bound
        rw [if_pos h_count]
      · constructor
        · intro h_no
          rw [if_neg] at h_no
          · by_contra h_bool
            have h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                           ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
              exact exists_exchange_of_sufficient_evens lst1 lst2 h_ne1 h_ne2 |>.mp h_bool |>.1
            exact h_no h_count
          · rw [not_le]
            by_contra h_le
            have h_exists := exists_exchange_of_sufficient_evens lst1 lst2 h_ne1 h_ne2 h_le
            rw [if_pos h_le] at h_no
            exact h_no
        · intro h_neither
          by_cases h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                             ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length
          · rw [if_pos h_count] at h_neither
            exact h_neither.1 rfl
          · rw [if_neg h_count] at h_neither
            exact h_neither.2 rfl
    · rw [not_or]
      constructor
      · rw [List.not_isEmpty_iff]
        exact h_ne1
      · rw [List.not_isEmpty_iff]
        exact h_ne2