def problem_spec
(implementation: List (List Int) → Int → List (Nat × Nat))
(lst: List (List Int))
(x: Int) :=
let spec (result : List (Nat × Nat)) :=
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    row < lst.length ∧
    col < lst[row]!.length ∧
    (lst[row]!)[col]! = x) ∧
  (∀ (i < lst.length) (j < lst[i]!.length),
    (lst[i]!)[j]! = x → (i, j) ∈ result) ∧
  (result.map (fun (r, c) => r)).Sorted Nat.le ∧
  (∀ i < result.length,
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (fun a b => a ≥ b))
∃ result,
  implementation lst x = result ∧
  spec result

-- LLM HELPER
def find_positions_in_row (row: List Int) (x: Int) (row_idx: Nat) : List (Nat × Nat) :=
  (row.enum.filter (fun (_, val) => val = x)).map (fun (col_idx, _) => (row_idx, col_idx))

-- LLM HELPER
def find_all_positions (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  (lst.enum.map (fun (row_idx, row) => find_positions_in_row row x row_idx)).join

-- LLM HELPER  
def sort_positions (positions: List (Nat × Nat)) : List (Nat × Nat) :=
  positions.mergeSort (fun (r1, c1) (r2, c2) => 
    if r1 = r2 then c1 ≥ c2 else r1 ≤ r2)

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) := 
  sort_positions (find_all_positions lst x)

-- LLM HELPER
lemma find_positions_in_row_correct (row: List Int) (x: Int) (row_idx: Nat) :
  ∀ (col_idx val), (col_idx, val) ∈ row.enum → 
  (val = x ↔ (row_idx, col_idx) ∈ find_positions_in_row row x row_idx) := by
  intro col_idx val h
  constructor
  · intro h_eq
    simp [find_positions_in_row]
    exact ⟨⟨col_idx, val, h, h_eq⟩, rfl⟩
  · intro h_mem
    simp [find_positions_in_row] at h_mem
    obtain ⟨⟨_, _, _, h_eq⟩, _⟩ := h_mem
    exact h_eq

-- LLM HELPER
lemma find_all_positions_correct (lst: List (List Int)) (x: Int) :
  ∀ i j, i < lst.length → j < lst[i]!.length → 
  ((lst[i]!)[j]! = x ↔ (i, j) ∈ find_all_positions lst x) := by
  intro i j hi hj
  constructor
  · intro h_eq
    simp [find_all_positions]
    use i, lst[i]!, ⟨i, lst[i]!⟩
    constructor
    · exact List.mem_enum_of_mem ⟨List.get_mem lst i hi, rfl⟩
    · simp [find_positions_in_row]
      use j, (lst[i]!)[j]!
      constructor
      · exact List.mem_enum_of_mem (List.get_mem lst[i]! j hj)
      · exact ⟨h_eq, rfl⟩
  · intro h_mem
    simp [find_all_positions] at h_mem
    obtain ⟨row_idx, row, ⟨h_enum, h_eq⟩, h_pos⟩ := h_mem
    simp [find_positions_in_row] at h_pos
    obtain ⟨col_idx, val, h_val_enum, h_val_eq, h_pair⟩ := h_pos
    cases h_pair
    cases h_eq
    have h_row_eq : row = lst[i]! := by
      rw [List.mem_enum_iff] at h_enum
      obtain ⟨_, h_get⟩ := h_enum
      exact h_get.symm
    rw [h_row_eq] at h_val_enum h_val_eq
    have h_col_eq : col_idx = j := by
      rw [List.mem_enum_iff] at h_val_enum
      obtain ⟨_, h_get⟩ := h_val_enum
      have : val = (lst[i]!)[j]! := h_get.symm
      rw [this] at h_val_eq
      sorry -- Need to prove col_idx = j from enum membership
    rw [h_col_eq] at h_val_eq
    exact h_val_eq

-- LLM HELPER
lemma sort_positions_preserves_membership (positions: List (Nat × Nat)) :
  ∀ p, p ∈ positions ↔ p ∈ sort_positions positions := by
  intro p
  simp [sort_positions]
  exact List.mem_mergeSort

-- LLM HELPER
lemma sort_positions_sorted (positions: List (Nat × Nat)) :
  let result := sort_positions positions
  (result.map (fun (r, c) => r)).Sorted Nat.le ∧
  (∀ i < result.length,
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (fun a b => a ≥ b)) := by
  constructor
  · simp [sort_positions]
    apply List.Sorted.map
    apply List.mergeSort_sorted
    intro a b c h1 h2
    cases a with | mk r1 c1 =>
    cases b with | mk r2 c2 =>
    cases c with | mk r3 c3 =>
    simp at h1 h2
    cases h1 with
    | inl h1 => cases h2 with
      | inl h2 => exact Nat.le_trans h1 h2
      | inr h2 => exact Nat.le_of_lt (Nat.lt_of_le_of_lt h1 h2)
    | inr h1 => cases h2 with
      | inl h2 => simp at h1 h2; rw [h1] at h2; exact h2
      | inr h2 => simp at h1 h2; rw [h1]; exact h2
  · intro i hi
    simp [sort_positions]
    sorry -- Complex proof about column sorting within rows

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x := by
  simp [problem_spec]
  use implementation lst x
  constructor
  · rfl
  · constructor
    · intro i hi
      simp [implementation]
      sorry -- Prove bounds and correctness
    · constructor
      · intro i hi j hj h_eq
        simp [implementation]
        rw [sort_positions_preserves_membership]
        exact (find_all_positions_correct lst x i j hi hj).mp h_eq
      · exact sort_positions_sorted (find_all_positions lst x)