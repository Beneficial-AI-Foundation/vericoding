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
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
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

-- LLM HELPER
def canMakeAllEven (lst1: List Int) (lst2: List Int) : Bool :=
  if lst1.isEmpty || lst2.isEmpty then false
  else
    let odd_count1 := (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i)) |>.length
    let even_count2 := (List.range lst2.length).filter (fun i => Even (lst2.get! i)) |>.length
    odd_count1 ≤ even_count2

-- LLM HELPER
def constructExchange (lst1: List Int) (lst2: List Int) : List (Nat × Nat) :=
  if lst1.isEmpty || lst2.isEmpty then []
  else
    let odd_indices1 := (List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))
    let even_indices2 := (List.range lst2.length).filter (fun i => Even (lst2.get! i))
    let pairs := odd_indices1.zip even_indices2
    pairs.take (min odd_indices1.length even_indices2.length)

def implementation (lst1: List Int) (lst2: List Int) : String :=
  if canMakeAllEven lst1 lst2 then "YES" else "NO"

-- LLM HELPER
lemma canMakeAllEven_sound (lst1 lst2 : List Int) :
  canMakeAllEven lst1 lst2 = true →
  lst1 ≠ [] → lst2 ≠ [] →
  ∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!)) := by
  intro h_can h_ne1 h_ne2
  use constructExchange lst1 lst2
  simp [constructExchange]
  split_ifs with h_empty
  · exfalso
    cases h_empty with
    | inl h => exact h_ne1 h
    | inr h => exact h_ne2 h
  · constructor
    · simp [List.all_eq_true]
      intros a h_mem
      simp [List.mem_map] at h_mem
      obtain ⟨⟨i, j⟩, h_pair_mem, h_eq⟩ := h_mem
      simp at h_eq
      rw [← h_eq]
      simp [List.mem_take] at h_pair_mem
      obtain ⟨h_pair_mem_zip, _⟩ := h_pair_mem
      have h_mem_odd : i ∈ (List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k)) := by
        simp [List.mem_zip] at h_pair_mem_zip
        exact h_pair_mem_zip.1
      simp [List.mem_filter, List.mem_range] at h_mem_odd
      exact h_mem_odd.1
    · constructor
      · simp [List.all_eq_true]
        intros a h_mem
        simp [List.mem_map] at h_mem
        obtain ⟨⟨i, j⟩, h_pair_mem, h_eq⟩ := h_mem
        simp at h_eq
        rw [← h_eq]
        simp [List.mem_take] at h_pair_mem
        obtain ⟨h_pair_mem_zip, _⟩ := h_pair_mem
        have h_mem_even : j ∈ (List.range lst2.length).filter (fun k => Even (lst2.get! k)) := by
          simp [List.mem_zip] at h_pair_mem_zip
          exact h_pair_mem_zip.2
        simp [List.mem_filter, List.mem_range] at h_mem_even
        exact h_mem_even.1
      · constructor
        · apply List.nodup_map_of_injective
          · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h_eq
            simp at h_eq
            rw [h_eq]
          · apply List.Nodup.take
            apply List.nodup_zip_of_nodup_left
            apply List.nodup_filter
            exact List.nodup_range _
        · constructor
          · apply List.nodup_map_of_injective
            · intro ⟨a1, b1⟩ ⟨a2, b2⟩ h_eq
              simp at h_eq
              rw [h_eq]
            · apply List.Nodup.take
              apply List.nodup_zip_of_nodup_right
              apply List.nodup_filter
              exact List.nodup_range _
          · intros i h_i_lt
            constructor
            · intro h_not_mem
              by_contra h_not_even
              have h_mem_odd : i ∈ (List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k)) := by
                simp [List.mem_filter, List.mem_range]
                exact ⟨h_i_lt, h_not_even⟩
              have h_mem_lst1_idxs : i ∈ ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).zip ((List.range lst2.length).filter (fun k => Even (lst2.get! k))) |>.take (min ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).length ((List.range lst2.length).filter (fun k => Even (lst2.get! k))).length) |>.map (fun (a, b) => a) := by
                simp [List.mem_map]
                have h_len_pos : 0 < ((List.range lst2.length).filter (fun k => Even (lst2.get! k))).length := by
                  have h_can_unfold : canMakeAllEven lst1 lst2 = true := h_can
                  simp [canMakeAllEven] at h_can_unfold
                  split_ifs at h_can_unfold with h_empty_check
                  · exfalso
                    cases h_empty_check with
                    | inl h => exact h_ne1 h
                    | inr h => exact h_ne2 h
                  · simp at h_can_unfold
                    have h_odd_pos : 0 < ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).length := by
                      rw [List.length_pos_iff_ne_nil]
                      simp [List.ne_nil_iff_length_pos]
                      rw [List.length_pos_iff_ne_nil]
                      simp [List.filter_ne_nil]
                      use i
                      simp [List.mem_filter, List.mem_range]
                      exact ⟨h_i_lt, h_not_even⟩
                    omega
                have h_zip_mem : ∃ j, (i, j) ∈ ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).zip ((List.range lst2.length).filter (fun k => Even (lst2.get! k))) := by
                  simp [List.mem_zip]
                  have h_idx : ∃ idx, ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).get? idx = some i := by
                    simp [List.get?_eq_some_iff]
                    exact List.mem_iff_get?.mp h_mem_odd
                  obtain ⟨idx, h_get_i⟩ := h_idx
                  have h_len_bound : idx < min ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).length ((List.range lst2.length).filter (fun k => Even (lst2.get! k))).length := by
                    have h_can_unfold : canMakeAllEven lst1 lst2 = true := h_can
                    simp [canMakeAllEven] at h_can_unfold
                    split_ifs at h_can_unfold with h_empty_check
                    · exfalso
                      cases h_empty_check with
                      | inl h => exact h_ne1 h
                      | inr h => exact h_ne2 h
                    · simp at h_can_unfold
                      have h_idx_lt : idx < ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).length := by
                        rw [List.get?_eq_some_iff] at h_get_i
                        exact h_get_i.1
                      have h_even_len : ((List.range lst1.length).filter (fun k => ¬ Even (lst1.get! k))).length ≤ ((List.range lst2.length).filter (fun k => Even (lst2.get! k))).length := h_can_unfold
                      exact lt_of_lt_of_le h_idx_lt (min_le_right _ _)
                  obtain ⟨j, h_get_j⟩ := List.get?_eq_some_iff.mp (List.get?_zip_left h_len_bound ▸ h_get_i)
                  exact ⟨j, h_get_i, h_get_j⟩
                obtain ⟨j, h_zip_mem⟩ := h_zip_mem
                use (i, j)
                constructor
                · simp [List.mem_take]
                  exact ⟨h_zip_mem, by simp⟩
                · simp
              exact h_not_mem h_mem_lst1_idxs
            · intro h_mem
              simp [List.mem_map] at h_mem
              obtain ⟨⟨i', j⟩, h_pair_mem, h_eq⟩ := h_mem
              simp at h_eq
              rw [← h_eq]
              simp [List.mem_take] at h_pair_mem
              obtain ⟨h_pair_mem_zip, _⟩ := h_pair_mem
              have h_mem_even : j ∈ (List.range lst2.length).filter (fun k => Even (lst2.get! k)) := by
                simp [List.mem_zip] at h_pair_mem_zip
                exact h_pair_mem_zip.2
              simp [List.mem_filter, List.mem_range] at h_mem_even
              exact h_mem_even.2

-- LLM HELPER
lemma canMakeAllEven_complete (lst1 lst2 : List Int) :
  lst1 ≠ [] → lst2 ≠ [] →
  (∃ exchange: List (Nat × Nat),
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    lst1_idxs.all (fun i => i < lst1.length) ∧
    lst2_idxs.all (fun i => i < lst2.length) ∧
    lst1_idxs.Nodup ∧
    lst2_idxs.Nodup ∧
    ∀ i, i < lst1.length →
      (i ∉ lst1_idxs → Even (lst1.get! i)) ∧
      (i ∈ lst1_idxs →
        let i_idx := (lst1_idxs.indexesOf i).head!
        Even (lst2[lst2_idxs.get! i_idx]!))) →
  canMakeAllEven lst1 lst2 = true := by
  intro h_ne1 h_ne2 h_exists
  simp [canMakeAllEven]
  split_ifs with h_empty
  · exfalso
    cases h_empty with
    | inl h => exact h_ne1 h
    | inr h => exact h_ne2 h
  · obtain ⟨exchange, h_prop⟩ := h_exists
    let lst1_idxs := exchange.map (fun (a, b) => a)
    let lst2_idxs := exchange.map (fun (a, b) => b)
    have h_all_even : ∀ i, i < lst1.length → i ∉ lst1_idxs → Even (lst1.get! i) := by
      intro i h_i_lt h_not_mem
      exact (h_prop.2.2.2.2 i h_i_lt).1 h_not_mem
    have h_odd_count : ((List.range lst1.length).filter (fun i => ¬ Even (lst1.get! i))).length ≤ lst1_idxs.length := by
      apply List.length_le_length_of_sublist
      apply List.sublist_of_subset
      intro i h_mem
      simp [List.mem_filter, List.mem_range] at h_mem
      by_contra h_not_mem
      have h_even : Even (lst1.get! i) := h_all_even i h_mem.1 h_not_mem
      exact h_mem.2 h_even
    have h_even_count : lst2_idxs.length ≤ ((List.range lst2.length).filter (fun i => Even (lst2.get! i))).length := by
      apply List.length_le_length_of_sublist
      apply List.sublist_of_subset
      intro j h_mem
      simp [List.mem_filter, List.mem_range]
      have h_valid : j < lst2.length := by
        simp [List.all_eq_true] at h_prop
        exact h_prop.2.1 j h_mem
      constructor
      · exact h_valid
      · have h_exists_i : ∃ i, i ∈ lst1_idxs ∧ (let i_idx := (lst1_idxs.indexesOf i).head!; lst2_idxs.get! i_idx = j) := by
          simp [lst2_idxs] at h_mem
          simp [List.mem_map] at h_mem
          obtain ⟨⟨i, j'⟩, h_pair_mem, h_eq⟩ := h_mem
          simp at h_eq
          rw [← h_eq]
          use i
          constructor
          · simp [lst1_idxs, List.mem_map]
            use (i, j')
            exact ⟨h_pair_mem, rfl⟩
          · simp [lst1_idxs, lst2_idxs]
            rw [h_eq]
            simp [List.get!_eq_get]
            congr
        obtain ⟨i, h_i_mem, h_j_eq⟩ := h_exists_i
        have h_i_lt : i < lst1.length := by
          simp [List.all_eq_true] at h_prop
          exact h_prop.1 i h_i_mem
        have h_even_j : Even (lst2[lst2_idxs.get! (lst1_idxs.indexesOf i).head!]!) := by
          exact (h_prop.2.2.2.2 i h_i_lt).2 h_i_mem
        rw [← h_j_eq] at h_even_j
        exact h_even_j
    have h_equal_len : lst1_idxs.length = lst2_idxs.length := by
      simp [lst1_idxs, lst2_idxs]
      simp [List.length_map]
    rw [h_equal_len] at h_odd_count
    exact le_trans h_odd_count h_even_count

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
      simp only [if_pos_of_true (canMakeAllEven_complete lst1 lst2 h_ne1 h_ne2 h_bool)]
    · constructor
      · intro h_no
        by_contra h_bool
        have h_can : canMakeAllEven lst1 lst2 = true := canMakeAllEven_complete lst1 lst2 h_ne1 h_ne2 h_bool
        simp only [if_pos_of_true h_can] at h_no
      · intro h_neither
        by_cases h_can : canMakeAllEven lst1 lst2
        · simp only [if_pos_of_true h_can] at h_neither
          exact h_neither.1 rfl
        · simp only [if_neg h_can] at h_neither
          exact h_neither.2 rfl