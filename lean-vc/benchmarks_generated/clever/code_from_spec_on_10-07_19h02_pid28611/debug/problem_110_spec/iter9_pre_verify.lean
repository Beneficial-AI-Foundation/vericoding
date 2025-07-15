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
lemma Bool.not_or_eq_not_and_not (a b : Bool) : ¬(a || b) = (¬a && ¬b) := by
  cases a <;> cases b <;> simp

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
                use (i, j)
                exact ⟨h_pair_mem, rfl⟩
              have h_i_lt : i < lst1.length := by
                rw [List.all_eq_true_iff] at h_prop
                rw [decide_lt_eq_true_iff]
                exact h_prop.1 i h_i_mem
              have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
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
                  use (i, j)
                  exact ⟨h_pair_mem, rfl⟩
                have h_i_lt : i < lst1.length := by
                  rw [List.all_eq_true_iff] at h_prop
                  rw [decide_lt_eq_true_iff]
                  exact h_prop.1 i h_i_mem
                have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
                  exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
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