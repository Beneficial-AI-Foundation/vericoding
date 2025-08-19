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
  (∀ (i : Nat) (hi : i < lst.length) (j : Nat) (hj : j < lst[i]!.length),
    (lst[i]!)[j]! = x → (i, j) ∈ result) ∧
  (result.map (fun (r, c) => r)).Sorted (· ≤ ·) ∧
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (· ≥ ·))
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
  ∀ col_idx, col_idx < row.length → 
  (row[col_idx]! = x ↔ (row_idx, col_idx) ∈ find_positions_in_row row x row_idx) := by
  intro col_idx h
  constructor
  · intro h_eq
    simp [find_positions_in_row]
    use col_idx, row[col_idx]!
    constructor
    · simp [List.mem_enum]
      exact ⟨h, rfl⟩
    · exact ⟨h_eq, rfl⟩
  · intro h_mem
    simp [find_positions_in_row] at h_mem
    obtain ⟨idx, val, h_enum, h_eq, h_pair⟩ := h_mem
    simp [List.mem_enum] at h_enum
    obtain ⟨_, h_get⟩ := h_enum
    cases h_pair
    exact h_eq

-- LLM HELPER
lemma find_all_positions_correct (lst: List (List Int)) (x: Int) :
  ∀ i j, i < lst.length → j < lst[i]!.length → 
  ((lst[i]!)[j]! = x ↔ (i, j) ∈ find_all_positions lst x) := by
  intro i j hi hj
  constructor
  · intro h_eq
    simp [find_all_positions]
    use i, lst[i]!
    constructor
    · simp [List.mem_enum]
      exact ⟨hi, rfl⟩
    · exact (find_positions_in_row_correct (lst[i]!) x i j hj).mp h_eq
  · intro h_mem
    simp [find_all_positions] at h_mem
    obtain ⟨row_idx, row, h_enum, h_pos⟩ := h_mem
    simp [List.mem_enum] at h_enum
    obtain ⟨_, h_get⟩ := h_enum
    rw [← h_get] at h_pos
    exact (find_positions_in_row_correct (lst[i]!) x i j hj).mpr h_pos

-- LLM HELPER
lemma sort_positions_preserves_membership (positions: List (Nat × Nat)) :
  ∀ p, p ∈ positions ↔ p ∈ sort_positions positions := by
  intro p
  simp [sort_positions]
  exact List.mem_mergeSort

-- LLM HELPER
lemma sort_positions_sorted (positions: List (Nat × Nat)) :
  let result := sort_positions positions
  (result.map (fun (r, c) => r)).Sorted (· ≤ ·) ∧
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (· ≥ ·)) := by
  constructor
  · simp [sort_positions]
    apply List.Sorted.map
    apply List.mergeSort_sorted
    intro a b c h1 h2
    cases a with | mk r1 c1 =>
    cases b with | mk r2 c2 =>
    cases c with | mk r3 c3 =>
    simp at h1 h2
    by_cases h : r1 = r2
    · simp [h] at h1
      by_cases h' : r2 = r3
      · simp [h'] at h2
        rw [h, h']
      · simp [h'] at h2
        rw [h]
        exact h2
    · simp [h] at h1
      by_cases h' : r2 = r3
      · simp [h'] at h2
        rw [← h']
        exact h1
      · simp [h'] at h2
        exact Nat.le_trans h1 h2
  · intro i hi
    simp [sort_positions]
    apply List.Sorted.map
    apply List.mergeSort_sorted
    intro a b c h1 h2
    cases a with | mk r1 c1 =>
    cases b with | mk r2 c2 =>
    cases c with | mk r3 c3 =>
    simp at h1 h2
    exact Nat.le_trans h2 h1

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
      obtain ⟨row, col⟩ := (sort_positions (find_all_positions lst x))[i]!
      constructor
      · simp [sort_positions] at hi
        have h_mem : (row, col) ∈ find_all_positions lst x := by
          rw [← sort_positions_preserves_membership]
          exact List.get_mem _ _ hi
        simp [find_all_positions] at h_mem
        obtain ⟨row_idx, lst_row, h_enum, h_pos⟩ := h_mem
        simp [List.mem_enum] at h_enum
        obtain ⟨h_bound, _⟩ := h_enum
        exact h_bound
      · constructor
        · simp [sort_positions] at hi
          have h_mem : (row, col) ∈ find_all_positions lst x := by
            rw [← sort_positions_preserves_membership]
            exact List.get_mem _ _ hi
          simp [find_all_positions] at h_mem
          obtain ⟨row_idx, lst_row, h_enum, h_pos⟩ := h_mem
          simp [find_positions_in_row] at h_pos
          obtain ⟨col_idx, val, h_enum_inner, _, _⟩ := h_pos
          simp [List.mem_enum] at h_enum_inner
          obtain ⟨h_bound, _⟩ := h_enum_inner
          exact h_bound
        · simp [sort_positions] at hi
          have h_mem : (row, col) ∈ find_all_positions lst x := by
            rw [← sort_positions_preserves_membership]
            exact List.get_mem _ _ hi
          simp [find_all_positions] at h_mem
          obtain ⟨row_idx, lst_row, h_enum, h_pos⟩ := h_mem
          simp [find_positions_in_row] at h_pos
          obtain ⟨col_idx, val, h_enum_inner, h_eq, _⟩ := h_pos
          exact h_eq
    · constructor
      · intro i hi j hj h_eq
        simp [implementation]
        rw [sort_positions_preserves_membership]
        exact (find_all_positions_correct lst x i j hi hj).mp h_eq
      · exact sort_positions_sorted (find_all_positions lst x)