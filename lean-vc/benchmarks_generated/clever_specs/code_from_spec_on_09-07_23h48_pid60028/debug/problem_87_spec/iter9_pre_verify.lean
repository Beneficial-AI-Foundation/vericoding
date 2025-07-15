-- LLM HELPER
def List.Sorted (r : α → α → Prop) (l : List α) : Prop :=
  List.Pairwise r l

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
def find_in_row (row: List Int) (x: Int) (row_idx: Nat) : List (Nat × Nat) :=
  (List.range row.length).filter (fun j => row[j]! = x) |>.map (fun j => (row_idx, j)) |>.reverse

-- LLM HELPER
def find_all_occurrences (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  (List.range lst.length).foldl (fun acc i => 
    acc ++ find_in_row lst[i]! x i) []

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  find_all_occurrences lst x

-- LLM HELPER
lemma find_in_row_mem_iff (row: List Int) (x: Int) (row_idx: Nat) (r c: Nat) :
  (r, c) ∈ find_in_row row x row_idx ↔ r = row_idx ∧ c < row.length ∧ row[c]! = x := by
  simp [find_in_row, List.mem_reverse, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · intro ⟨j, hj_range, hj_val, hj_eq⟩
    simp at hj_eq
    exact ⟨hj_eq.1, hj_range, hj_val⟩
  · intro ⟨hr, hc_range, hc_val⟩
    use c
    exact ⟨hc_range, hc_val, hr, rfl⟩

-- LLM HELPER
lemma find_in_row_sorted (row: List Int) (x: Int) (row_idx: Nat) :
  List.Sorted (· ≥ ·) ((find_in_row row x row_idx).filter (fun (r, c) => r = row_idx)).map (fun (r, c) => c) := by
  simp [find_in_row]
  have h1 : ((List.range row.length).filter (fun j => row[j]! = x)).map (fun j => (row_idx, j)) |>.reverse.filter (fun (r, c) => r = row_idx) = ((List.range row.length).filter (fun j => row[j]! = x)).map (fun j => (row_idx, j)) |>.reverse := by
    apply List.filter_eq_self.mpr
    intro ⟨r, c⟩ h
    simp [List.mem_reverse, List.mem_map] at h
    obtain ⟨j, _, rfl⟩ := h
    simp
  rw [h1]
  simp [List.map_map]
  have h2 : List.Sorted (· ≥ ·) ((List.range row.length).filter (fun j => row[j]! = x)).reverse := by
    rw [List.Sorted]
    apply List.pairwise_reverse.mpr
    apply List.Pairwise.filter
    rw [← List.Sorted]
    exact List.sorted_range
  exact h2

-- LLM HELPER
lemma foldl_append_mem (lst: List (List Int)) (x: Int) (i: Nat) (hi: i < lst.length) (r c: Nat) :
  (r, c) ∈ find_in_row lst[i]! x i → (r, c) ∈ (List.range lst.length).foldl (fun acc j => acc ++ find_in_row lst[j]! x j) [] := by
  intro h
  have : (r, c) ∈ [] ++ find_in_row lst[i]! x i := by simp [h]
  apply List.foldl_append_mem_of_mem this
  exact List.mem_range.mpr hi

-- LLM HELPER
lemma foldl_append_mem_iff (lst: List (List Int)) (x: Int) (r c: Nat) :
  (r, c) ∈ (List.range lst.length).foldl (fun acc j => acc ++ find_in_row lst[j]! x j) [] ↔ 
  ∃ i < lst.length, (r, c) ∈ find_in_row lst[i]! x i := by
  constructor
  · intro h
    have := List.foldl_append_mem_iff.mp h
    obtain ⟨i, hi_mem, hi_elem⟩ := this
    use i
    simp [List.mem_range] at hi_mem
    exact ⟨hi_mem, hi_elem⟩
  · intro ⟨i, hi_bound, hi_mem⟩
    exact foldl_append_mem lst x i hi_bound r c hi_mem

-- LLM HELPER
lemma find_all_occurrences_mem_iff (lst: List (List Int)) (x: Int) (r c: Nat) :
  (r, c) ∈ find_all_occurrences lst x ↔ r < lst.length ∧ c < lst[r]!.length ∧ lst[r]![c]! = x := by
  simp [find_all_occurrences]
  rw [foldl_append_mem_iff]
  constructor
  · intro ⟨i, hi, h⟩
    rw [find_in_row_mem_iff] at h
    obtain ⟨hr, hc, hval⟩ := h
    rw [hr]
    exact ⟨hi, hc, hval⟩
  · intro ⟨hr, hc, hval⟩
    use r
    exact ⟨hr, find_in_row_mem_iff.mpr ⟨rfl, hc, hval⟩⟩

-- LLM HELPER
lemma find_all_occurrences_sorted_rows (lst: List (List Int)) (x: Int) :
  List.Sorted (· ≤ ·) (find_all_occurrences lst x).map (fun (r, c) => r) := by
  simp [find_all_occurrences]
  rw [List.Sorted]
  apply List.pairwise_foldl_append_map
  intro i hi
  simp [find_in_row]
  rw [List.Sorted]
  exact List.pairwise_repeat

-- LLM HELPER
lemma find_all_occurrences_sorted_cols (lst: List (List Int)) (x: Int) (i: Nat) (hi: i < (find_all_occurrences lst x).length) :
  let (row, col) := (find_all_occurrences lst x)[i]!
  List.Sorted (· ≥ ·) ((find_all_occurrences lst x).filter (fun (r, c) => r = row)).map (fun (r, c) => c) := by
  obtain ⟨row, col⟩ := (find_all_occurrences lst x)[i]!
  simp [find_all_occurrences]
  rw [List.Sorted]
  apply List.pairwise_foldl_append_filter
  intro j hj
  rw [← List.Sorted]
  exact find_in_row_sorted lst[j]! x j

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x := by
  use find_all_occurrences lst x
  constructor
  · rfl
  · constructor
    · intro i hi
      obtain ⟨row, col⟩ := (find_all_occurrences lst x)[i]!
      rw [find_all_occurrences_mem_iff] at *
      have h := List.get_mem (find_all_occurrences lst x) i hi
      rw [List.get_eq_getElem] at h
      simp at h
      exact h
    · constructor
      · intro i hi j hj hval
        rw [find_all_occurrences_mem_iff]
        exact ⟨hi, hj, hval⟩
      · constructor
        · exact find_all_occurrences_sorted_rows lst x
        · exact find_all_occurrences_sorted_cols lst x