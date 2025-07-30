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
lemma List.all_eq_true_iff {α : Type*} (l : List α) (p : α → Bool) :
  l.all p = true ↔ ∀ x ∈ l, p x = true := by
  rw [List.all_eq_true]

-- LLM HELPER
lemma decide_eq_true_iff_prop {p : Prop} [Decidable p] : decide p = true ↔ p := by
  rw [decide_eq_true_iff]

-- LLM HELPER
lemma decide_not_even_eq_true_iff {x : Int} : decide (¬Even x) = true ↔ ¬Even x := by
  rw [decide_eq_true_iff]

-- LLM HELPER
lemma decide_even_eq_true_iff {x : Int} : decide (Even x) = true ↔ Even x := by
  rw [decide_eq_true_iff]

-- LLM HELPER
lemma decide_lt_eq_true_iff {a b : Nat} : decide (a < b) = true ↔ a < b := by
  rw [decide_eq_true_iff]

-- LLM HELPER
lemma List.mem_map_exists {α β : Type*} (f : α → β) (l : List α) (b : β) :
  b ∈ l.map f ↔ ∃ a ∈ l, f a = b := by
  rw [List.mem_map]

-- LLM HELPER
lemma List.get!_map {α β : Type*} (f : α → β) (l : List α) (i : Nat) [Inhabited β] :
  i < l.length → (l.map f).get! i = f (l.get! i) := by
  intro h
  rw [List.get!_eq_get_of_valid]
  rw [List.get_map]
  rw [List.get!_eq_get_of_valid h]
  rw [List.length_map]
  exact h

-- LLM HELPER
lemma List.indexesOf_head_mem {α : Type*} [DecidableEq α] (a : α) (l : List α) :
  a ∈ l → (l.indexesOf a).head! < l.length := by
  intro h
  have h_ne : (l.indexesOf a) ≠ [] := List.indexesOf_ne_nil_of_mem h
  have h_mem : (l.indexesOf a).head! ∈ l.indexesOf a := by
    rw [List.head!_eq_head_of_ne_nil h_ne]
    exact List.head_mem (l.indexesOf a) h_ne
  exact List.mem_indexesOf_iff.mp h_mem

-- LLM HELPER
lemma List.get!_indexesOf_head {α : Type*} [DecidableEq α] (a : α) (l : List α) :
  a ∈ l → l.get! (l.indexesOf a).head! = a := by
  intro h
  have h_ne : (l.indexesOf a) ≠ [] := List.indexesOf_ne_nil_of_mem h
  have h_mem : (l.indexesOf a).head! ∈ l.indexesOf a := by
    rw [List.head!_eq_head_of_ne_nil h_ne]
    exact List.head_mem (l.indexesOf a) h_ne
  exact List.mem_indexesOf_iff.mp h_mem

theorem correctness
(lst1: List Int)
(lst2: List Int)
: problem_spec implementation lst1 lst2 := by
  use implementation lst1 lst2
  constructor
  · rfl
  · intro h_ne1 h_ne2
    simp only [implementation]
    have h_not_empty : ¬(lst1.isEmpty || lst2.isEmpty) := by
      simp [List.isEmpty_iff]
      exact ⟨h_ne1, h_ne2⟩
    rw [if_neg h_not_empty]
    constructor
    · intro h_bool
      by_cases h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                         ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length
      · rw [if_pos h_count]
      · rw [if_neg h_count]
        exfalso
        obtain ⟨exchange, h_prop⟩ := h_bool
        let lst1_idxs := exchange.map (fun (a, _) => a)
        let lst2_idxs := exchange.map (fun (_, b) => b)
        have h_all_odd_in_idxs : ∀ i, i < lst1.length → ¬ Even (lst1.get! i) → i ∈ lst1_idxs := by
          intro i h_i_lt h_not_even
          by_contra h_not_mem
          have h_even := (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
          exact h_not_even h_even
        have h_contradiction : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                                ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
          have h_odd_subset : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).toFinset ⊆ lst1_idxs.toFinset := by
            intro i h_mem
            rw [List.mem_toFinset] at h_mem ⊢
            rw [List.mem_filter, List.mem_range] at h_mem
            exact h_all_odd_in_idxs i h_mem.1 h_mem.2
          have h_card_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
            rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range _))]
            rw [← List.toFinset_card_of_nodup h_prop.2.2.1]
            exact Finset.card_le_card h_odd_subset
          have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
            simp only [List.length_map]
          rw [h_equal_len] at h_card_le
          have h_even_bound : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
            rw [← List.toFinset_card_of_nodup h_prop.2.2.2.1]
            rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range _))]
            apply Finset.card_le_card
            intro j h_mem
            rw [List.mem_toFinset] at h_mem ⊢
            rw [List.mem_filter, List.mem_range]
            rw [List.all_eq_true_iff] at h_prop
            have h_valid : j < lst2.length := by
              rw [List.all_eq_true_iff] at h_prop
              rw [decide_lt_eq_true_iff]
              exact h_prop.2.1 j h_mem
            constructor
            · exact h_valid
            · obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := (List.mem_map.mp h_mem)
              simp at h_eq
              subst h_eq
              have h_i_mem : i ∈ lst1_idxs := by
                rw [List.mem_map]
                use (i, j')
                exact ⟨h_pair_mem, rfl⟩
              have h_i_lt : i < lst1.length := by
                rw [List.all_eq_true_iff] at h_prop
                rw [decide_lt_eq_true_iff]
                exact h_prop.1 i h_i_mem
              have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
              have h_j_eq : j' = lst2_idxs.get! (lst1_idxs.indexesOf i).head! := by
                have h_index_lt : (lst1_idxs.indexesOf i).head! < lst1_idxs.length := by
                  exact List.indexesOf_head_mem i lst1_idxs h_i_mem
                have h_equal_length : lst1_idxs.length = exchange.length := by
                  simp [lst1_idxs]
                  exact List.length_map (fun (a, _) => a) exchange
                rw [h_equal_length] at h_index_lt
                have h_get_eq : lst1_idxs.get! (lst1_idxs.indexesOf i).head! = i := by
                  exact List.get!_indexesOf_head i lst1_idxs h_i_mem
                have h_pair_get : exchange.get! (lst1_idxs.indexesOf i).head! = (i, j') := by
                  have h_pair_fst : (exchange.get! (lst1_idxs.indexesOf i).head!).1 = i := by
                    rw [← List.get!_map (fun (a, _) => a) exchange (lst1_idxs.indexesOf i).head!]
                    exact h_get_eq
                    exact h_index_lt
                  have h_pair_snd : (exchange.get! (lst1_idxs.indexesOf i).head!).2 = j' := by
                    have h_j_get : lst2_idxs.get! (lst1_idxs.indexesOf i).head! = j' := by
                      rw [← List.get!_map (fun (_, b) => b) exchange (lst1_idxs.indexesOf i).head!]
                      simp [lst2_idxs]
                      rw [List.get!_map]
                      simp
                      rw [List.get!_eq_get_of_valid h_index_lt]
                      cases' exchange.get ⟨(lst1_idxs.indexesOf i).head!, h_index_lt⟩ with a b
                      simp at h_pair_fst
                      have h_eq_a : a = i := by
                        rw [← List.get!_eq_get_of_valid h_index_lt] at h_pair_fst
                        simp at h_pair_fst
                        exact h_pair_fst
                      subst h_eq_a
                      have h_pair_mem' : (i, b) ∈ exchange := by
                        rw [← List.get!_eq_get_of_valid h_index_lt]
                        exact List.get_mem _ _ _
                      have h_unique : (i, b) = (i, j') := by
                        have h_nodup : lst1_idxs.Nodup := h_prop.2.2.1
                        have h_i_unique : (lst1_idxs.indexesOf i).length = 1 := by
                          rw [List.length_indexesOf_eq_one_iff]
                          exact ⟨h_i_mem, h_nodup⟩
                        have h_head_eq : (lst1_idxs.indexesOf i).head! = (lst1_idxs.indexesOf i).head := by
                          rw [List.head!_eq_head_of_ne_nil]
                          exact List.indexesOf_ne_nil_of_mem h_i_mem
                        have h_index_zero : (lst1_idxs.indexesOf i).head! = (lst1_idxs.indexesOf i).get! 0 := by
                          rw [List.head!_eq_get!_zero]
                        rw [h_index_zero] at h_pair_mem'
                        have h_zero_lt : 0 < (lst1_idxs.indexesOf i).length := by
                          rw [h_i_unique]
                          norm_num
                        have h_get_zero : (lst1_idxs.indexesOf i).get! 0 = (lst1_idxs.indexesOf i).get ⟨0, h_zero_lt⟩ := by
                          rw [List.get!_eq_get_of_valid h_zero_lt]
                        have h_index_pos : (lst1_idxs.indexesOf i).get ⟨0, h_zero_lt⟩ < lst1_idxs.length := by
                          exact List.mem_indexesOf_iff.mp (List.get_mem _ _ _)
                        have h_at_index : lst1_idxs.get! (lst1_idxs.indexesOf i).get! 0 = i := by
                          rw [List.get!_eq_get_of_valid h_index_pos]
                          exact List.mem_indexesOf_iff.mp (List.get_mem _ _ _)
                        have h_map_eq : (exchange.get! (lst1_idxs.indexesOf i).get! 0).1 = i := by
                          rw [← List.get!_map (fun (a, _) => a) exchange (lst1_idxs.indexesOf i).get! 0]
                          exact h_at_index
                          rw [← h_get_zero, ← h_index_zero]
                          exact h_index_lt
                        rw [List.get!_eq_get_of_valid] at h_map_eq
                        cases' exchange.get ⟨(lst1_idxs.indexesOf i).get! 0, _⟩ with a' b'
                        simp at h_map_eq
                        subst h_map_eq
                        have h_get_eq' : exchange.get! (lst1_idxs.indexesOf i).get! 0 = (i, b') := by
                          rw [List.get!_eq_get_of_valid]
                          simp
                          rw [← h_get_zero, ← h_index_zero]
                          exact h_index_lt
                        rw [← h_get_zero, ← h_index_zero] at h_get_eq'
                        have h_pair_eq : (i, b) = (i, b') := by
                          rw [← List.get!_eq_get_of_valid h_index_lt] at h_pair_mem'
                          rw [h_get_eq'] at h_pair_mem'
                          injection h_pair_mem'
                        injection h_pair_eq with _ h_b_eq
                        subst h_b_eq
                        exact h_pair_mem.symm
                      injection h_unique with _ h_b_eq
                      exact h_b_eq.symm
                      exact h_index_lt
                    exact h_j_get
                  cases' exchange.get! (lst1_idxs.indexesOf i).head! with a b
                  simp at h_pair_fst h_pair_snd
                  subst h_pair_fst h_pair_snd
                  rfl
                rw [← List.get!_map (fun (_, b) => b) exchange (lst1_idxs.indexesOf i).head!]
                simp [lst2_idxs]
                rw [h_pair_get]
                simp
                exact h_index_lt
              rw [h_j_eq]
              exact h_even_j
          exact le_trans h_card_le h_even_bound
        exact h_count h_contradiction
    · constructor
      · intro h_no
        by_cases h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                           ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length
        · rw [if_pos h_count] at h_no
          simp at h_no
        · rw [if_neg h_count] at h_no
          intro h_exists
          have h_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                      ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
            obtain ⟨exchange, h_prop⟩ := h_exists
            let lst1_idxs := exchange.map (fun (a, _) => a)
            let lst2_idxs := exchange.map (fun (_, b) => b)
            have h_all_odd_in_idxs : ∀ i, i < lst1.length → ¬ Even (lst1.get! i) → i ∈ lst1_idxs := by
              intro i h_i_lt h_not_even
              by_contra h_not_mem
              have h_even := (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
              exact h_not_even h_even
            have h_odd_subset : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).toFinset ⊆ lst1_idxs.toFinset := by
              intro i h_mem
              rw [List.mem_toFinset] at h_mem ⊢
              rw [List.mem_filter, List.mem_range] at h_mem
              exact h_all_odd_in_idxs i h_mem.1 h_mem.2
            have h_card_le : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
              rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range _))]
              rw [← List.toFinset_card_of_nodup h_prop.2.2.1]
              exact Finset.card_le_card h_odd_subset
            have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
              simp only [List.length_map]
            rw [h_equal_len] at h_card_le
            have h_even_bound : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
              rw [← List.toFinset_card_of_nodup h_prop.2.2.2.1]
              rw [← List.toFinset_card_of_nodup (List.Nodup.filter _ (List.nodup_range _))]
              apply Finset.card_le_card
              intro j h_mem
              rw [List.mem_toFinset] at h_mem ⊢
              rw [List.mem_filter, List.mem_range]
              rw [List.all_eq_true_iff] at h_prop
              have h_valid : j < lst2.length := by
                rw [List.all_eq_true_iff] at h_prop
                rw [decide_lt_eq_true_iff]
                exact h_prop.2.1 j h_mem
              constructor
              · exact h_valid
              · obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := (List.mem_map.mp h_mem)
                simp at h_eq
                subst h_eq
                have h_i_mem : i ∈ lst1_idxs := by
                  rw [List.mem_map]
                  use (i, j')
                  exact ⟨h_pair_mem, rfl⟩
                have h_i_lt : i < lst1.length := by
                  rw [List.all_eq_true_iff] at h_prop
                  rw [decide_lt_eq_true_iff]
                  exact h_prop.1 i h_i_mem
                have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                  exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
                have h_j_eq : j' = lst2_idxs.get! (lst1_idxs.indexesOf i).head! := by
                  have h_index_lt : (lst1_idxs.indexesOf i).head! < lst1_idxs.length := by
                    exact List.indexesOf_head_mem i lst1_idxs h_i_mem
                  have h_equal_length : lst1_idxs.length = exchange.length := by
                    simp [lst1_idxs]
                    exact List.length_map (fun (a, _) => a) exchange
                  rw [h_equal_length] at h_index_lt
                  rw [← List.get!_map (fun (_, b) => b) exchange (lst1_idxs.indexesOf i).head!]
                  simp [lst2_idxs]
                  rw [List.get!_map]
                  simp
                  rw [List.get!_eq_get_of_valid h_index_lt]
                  cases' exchange.get ⟨(lst1_idxs.indexesOf i).head!, h_index_lt⟩ with a b
                  simp
                  have h_pair_mem' : (a, b) ∈ exchange := by
                    rw [← List.get!_eq_get_of_valid h_index_lt]
                    exact List.get_mem _ _ _
                  have h_get_fst : lst1_idxs.get! (lst1_idxs.indexesOf i).head! = a := by
                    rw [← List.get!_map (fun (a, _) => a) exchange (lst1_idxs.indexesOf i).head!]
                    simp [lst1_idxs]
                    rw [List.get!_map]
                    simp
                    rw [List.get!_eq_get_of_valid h_index_lt]
                    simp
                    exact h_index_lt
                  have h_a_eq : a = i := by
                    rw [← h_get_fst]
                    exact List.get!_indexesOf_head i lst1_idxs h_i_mem
                  subst h_a_eq
                  have h_unique : (i, b) = (i, j') := by
                    have h_nodup : lst1_idxs.Nodup := h_prop.2.2.1
                    have h_i_unique : (lst1_idxs.indexesOf i).length = 1 := by
                      rw [List.length_indexesOf_eq_one_iff]
                      exact ⟨h_i_mem, h_nodup⟩
                    have h_head_unique : ∀ p ∈ exchange, p.1 = i → p = (i, j') := by
                      intro p h_p_mem h_p_fst
                      cases' p with p1 p2
                      simp at h_p_fst
                      subst h_p_fst
                      have h_p_in_map : p1 ∈ lst1_idxs := by
                        rw [List.mem_map]
                        use (p1, p2)
                        exact ⟨h_p_mem, rfl⟩
                      have h_p1_eq : p1 = i := rfl
                      subst h_p1_eq
                      have h_i_in_map : i ∈ lst1_idxs := by
                        rw [List.mem_map]
                        use (i, p2)
                        exact ⟨h_p_mem, rfl⟩
                      have h_same_index : (lst1_idxs.indexesOf i).indexOf ((lst1_idxs.indexesOf i).head!) = 0 := by
                        rw [List.indexOf_head!_eq_zero]
                        exact List.indexesOf_ne_nil_of_mem h_i_mem
                      have h_j_in_map : j' ∈ lst2_idxs := by
                        rw [List.mem_map]
                        use (i, j')
                        exact ⟨h_pair_mem, rfl⟩
                      have h_p2_in_map : p2 ∈ lst2_idxs := by
                        rw [List.mem_map]
                        use (i, p2)
                        exact ⟨h_p_mem, rfl⟩
                      have h_nodup2 : lst2_idxs.Nodup := h_prop.2.2.2.1
                      have h_index_same : (lst1_idxs.indexesOf i).get! 0 = (lst1_idxs.indexesOf i).head! := by
                        rw [List.get!_zero_eq_head!]
                      have h_length_one : (lst1_idxs.indexesOf i).length = 1 := by
                        rw [List.length_indexesOf_eq_one_iff]
                        exact ⟨h_i_mem, h_nodup⟩
                      have h_unique_index : ∀ idx ∈ lst1_idxs.indexesOf i, idx = (lst1_idxs.indexesOf i).head! := by
                        intro idx h_idx_mem
                        have h_length_pos : 0 < (lst1_idxs.indexesOf i).length := by
                          rw [List.length_pos_iff_ne_nil]
                          exact List.indexesOf_ne_nil_of_mem h_i_mem
                        have h_idx_zero : idx = (lst1_idxs.indexesOf i).get! 0 := by
                          rw [List.length_eq_one] at h_length_one
                          obtain ⟨x, h_eq⟩ := h_length_one
                          rw [h_eq] at h_idx_mem
                          simp at h_idx_mem
                          subst h_idx_mem
                          rw [h_eq]
                          simp
                        rw [h_idx_zero, h_index_same]
                      rfl
                    exact h_unique h_pair_mem' rfl
                  injection h_unique with _ h_b_eq
                  exact h_b_eq.symm
                  exact h_index_lt
                rw [← h_j_eq]
                exact h_even_j
            exact le_trans h_card_le h_even_bound
          exact h_count h_le
      · intro h_neither
        by_cases h_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ 
                           ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length
        · rw [if_pos h_count] at h_neither
          exact h_neither.1 rfl
        · rw [if_neg h_count] at h_neither
          exact h_neither.2 rfl