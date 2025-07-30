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
def find_in_row (row: List Int) (x: Int) (row_idx: Nat) : List (Nat × Nat) :=
  List.range row.length |>.filter (fun j => row[j]! = x) |>.map (fun j => (row_idx, j)) |>.reverse

-- LLM HELPER
def find_all_occurrences (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  List.range lst.length |>.foldl (fun acc i => 
    acc ++ find_in_row lst[i]! x i) []

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  find_all_occurrences lst x

-- LLM HELPER
lemma find_in_row_correct (row: List Int) (x: Int) (row_idx: Nat) :
  ∀ (r, c) ∈ find_in_row row x row_idx, r = row_idx ∧ c < row.length ∧ row[c]! = x := by
  intro ⟨r, c⟩ h
  simp [find_in_row] at h
  obtain ⟨j, hj_mem, hj_eq⟩ := h
  simp [List.mem_map] at hj_mem
  obtain ⟨k, hk_mem, hk_eq⟩ := hj_mem
  simp [List.mem_filter] at hk_mem
  obtain ⟨hk_range, hk_val⟩ := hk_mem
  simp [List.mem_range] at hk_range
  simp at hj_eq hk_eq
  rw [←hj_eq, ←hk_eq]
  exact ⟨rfl, hk_range, hk_val⟩

-- LLM HELPER
lemma find_in_row_complete (row: List Int) (x: Int) (row_idx: Nat) :
  ∀ j < row.length, row[j]! = x → (row_idx, j) ∈ find_in_row row x row_idx := by
  intro j hj_bound hj_val
  simp [find_in_row]
  use j
  simp [List.mem_map]
  use j
  simp [List.mem_filter, List.mem_range]
  exact ⟨hj_bound, hj_val, rfl⟩

-- LLM HELPER
lemma find_in_row_sorted (row: List Int) (x: Int) (row_idx: Nat) :
  ((find_in_row row x row_idx).filter (fun (r, c) => r = row_idx)).map (fun (r, c) => c) |>.Sorted (fun a b => a ≥ b) := by
  simp [find_in_row]
  have h : (List.range row.length).filter (fun j => row[j]! = x) |>.reverse.Sorted (fun a b => a ≥ b) := by
    apply List.sorted_reverse.mpr
    simp [List.Sorted]
    apply List.sorted_filter
    exact List.sorted_range
  exact h

-- LLM HELPER
lemma find_all_occurrences_correct (lst: List (List Int)) (x: Int) :
  ∀ i, i < (find_all_occurrences lst x).length →
    let (row, col) := (find_all_occurrences lst x)[i]!
    row < lst.length ∧
    col < lst[row]!.length ∧
    (lst[row]!)[col]! = x := by
  intro i hi
  simp [find_all_occurrences] at hi ⊢
  obtain ⟨row, col⟩ := (List.range lst.length).foldl (fun acc i => acc ++ find_in_row lst[i]! x i) [][i]!
  sorry

-- LLM HELPER
lemma find_all_occurrences_complete (lst: List (List Int)) (x: Int) :
  ∀ (i < lst.length) (j < lst[i]!.length),
    (lst[i]!)[j]! = x → (i, j) ∈ find_all_occurrences lst x := by
  intro i hi j hj hval
  simp [find_all_occurrences]
  sorry

-- LLM HELPER
lemma find_all_occurrences_row_sorted (lst: List (List Int)) (x: Int) :
  ((find_all_occurrences lst x).map (fun (r, c) => r)).Sorted Nat.le := by
  simp [find_all_occurrences]
  sorry

-- LLM HELPER
lemma find_all_occurrences_col_sorted (lst: List (List Int)) (x: Int) :
  ∀ i < (find_all_occurrences lst x).length,
    let (row, col) := (find_all_occurrences lst x)[i]!
    (((find_all_occurrences lst x).filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (fun a b => a ≥ b) := by
  intro i hi
  simp [find_all_occurrences]
  sorry

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x := by
  use find_all_occurrences lst x
  constructor
  · rfl
  · constructor
    · exact find_all_occurrences_correct lst x
    · constructor
      · exact find_all_occurrences_complete lst x
      · constructor
        · exact find_all_occurrences_row_sorted lst x
        · exact find_all_occurrences_col_sorted lst x