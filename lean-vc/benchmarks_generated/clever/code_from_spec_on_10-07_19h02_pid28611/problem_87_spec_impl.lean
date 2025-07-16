import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

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
  (∀ (i : Nat) (j : Nat), i < lst.length → j < lst[i]!.length →
    (lst[i]!)[j]! = x → (i, j) ∈ result) ∧
  (result.map (fun (r, _) => r)).Sorted Nat.le ∧
  (∀ i, i < result.length →
    let (row, _) := result[i]!
    ((result.filter (fun (r, _) => r = row)).map (fun (_, c) => c)).Sorted (fun a b => a ≥ b))
∃ result,
  implementation lst x = result ∧
  spec result

-- LLM HELPER
def findInRow (row: List Int) (x: Int) (rowIdx: Nat) : List (Nat × Nat) :=
  (row.enum.filter (fun (_, val) => val = x)).map (fun (colIdx, _) => (rowIdx, colIdx))

-- LLM HELPER
def findAllOccurrences (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  (lst.enum.map (fun (rowIdx, row) => findInRow row x rowIdx)).flatten

-- LLM HELPER
def sortByRowThenCol (positions: List (Nat × Nat)) : List (Nat × Nat) :=
  positions.mergeSort (fun (r1, c1) (r2, c2) => 
    if r1 = r2 then c1 ≥ c2 else r1 ≤ r2)

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) := 
  sortByRowThenCol (findAllOccurrences lst x)

-- LLM HELPER
lemma findInRow_correct (row: List Int) (x: Int) (rowIdx: Nat) :
  ∀ (colIdx: Nat), (rowIdx, colIdx) ∈ findInRow row x rowIdx ↔ 
  (colIdx < row.length ∧ row[colIdx]! = x) := by
  intro colIdx
  simp [findInRow]
  constructor
  · intro h
    simp [List.mem_map, List.mem_filter] at h
    obtain ⟨⟨ci, val⟩, ⟨hfilter, heq⟩⟩ := h
    simp at heq
    rw [←heq.2]
    simp [List.mem_filter] at hfilter
    have h_enum : (ci, val) ∈ row.enum := hfilter.1
    rw [List.mem_enum] at h_enum
    exact ⟨h_enum.1, by rw [←h_enum.2]; exact hfilter.2⟩
  · intro ⟨hlen, hval⟩
    simp [List.mem_map, List.mem_filter]
    use (colIdx, row[colIdx]!)
    constructor
    · simp [List.mem_filter]
      exact ⟨List.mem_enum.2 ⟨hlen, rfl⟩, hval⟩
    · simp

-- LLM HELPER
lemma findAllOccurrences_correct (lst: List (List Int)) (x: Int) :
  ∀ (rowIdx colIdx: Nat), (rowIdx, colIdx) ∈ findAllOccurrences lst x ↔ 
  (rowIdx < lst.length ∧ colIdx < lst[rowIdx]!.length ∧ (lst[rowIdx]!)[colIdx]! = x) := by
  intro rowIdx colIdx
  simp [findAllOccurrences]
  constructor
  · intro h
    simp [List.mem_flatten, List.mem_map] at h
    obtain ⟨⟨ri, row⟩, ⟨hmem, hin⟩⟩ := h
    rw [List.mem_enum] at hmem
    rw [findInRow_correct] at hin
    exact ⟨hmem.1, by rw [←hmem.2]; exact hin.1, by rw [←hmem.2]; exact hin.2⟩
  · intro ⟨hrow, hcol, hval⟩
    simp [List.mem_flatten, List.mem_map]
    use (rowIdx, lst[rowIdx]!)
    constructor
    · exact List.mem_enum.2 ⟨hrow, rfl⟩
    · rw [findInRow_correct]
      exact ⟨hcol, hval⟩

-- LLM HELPER
lemma sortByRowThenCol_preserves_membership (positions: List (Nat × Nat)) :
  ∀ p, p ∈ sortByRowThenCol positions ↔ p ∈ positions := by
  intro p
  simp [sortByRowThenCol]
  exact List.mem_mergeSort

-- LLM HELPER
lemma sortByRowThenCol_length (positions: List (Nat × Nat)) :
  (sortByRowThenCol positions).length = positions.length := by
  simp [sortByRowThenCol]
  exact List.length_mergeSort

-- LLM HELPER
lemma sortByRowThenCol_sorted (positions: List (Nat × Nat)) :
  List.Pairwise (fun (r1, c1) (r2, c2) => if r1 = r2 then c2 ≤ c1 else r1 ≤ r2) (sortByRowThenCol positions) := by
  simp [sortByRowThenCol]
  exact List.pairwise_mergeSort _ _ positions

-- LLM HELPER
lemma row_sorted_from_pairwise (positions: List (Nat × Nat)) :
  List.Pairwise (fun (r1, c1) (r2, c2) => if r1 = r2 then c2 ≤ c1 else r1 ≤ r2) positions →
  List.Sorted Nat.le (positions.map (fun (r, _) => r)) := by
  intro h
  rw [List.Sorted]
  apply List.Pairwise.imp _ h
  intro (r1, c1) (r2, c2) h_pair
  simp at h_pair
  by_cases h_eq : r1 = r2
  · rw [h_eq]
  · simp [h_eq] at h_pair
    exact h_pair

-- LLM HELPER
lemma col_sorted_within_row (positions: List (Nat × Nat)) (row: Nat) :
  List.Pairwise (fun (r1, c1) (r2, c2) => if r1 = r2 then c2 ≤ c1 else r1 ≤ r2) positions →
  List.Sorted (fun a b => a ≥ b) ((positions.filter (fun (r, _) => r = row)).map (fun (_, c) => c)) := by
  intro h
  rw [List.Sorted]
  apply List.Pairwise.imp _ (List.Pairwise.filter _ h)
  intro (r1, c1) (r2, c2) h_pair
  simp [List.mem_filter] at h_pair
  have hr1 : r1 = row := h_pair.1.2
  have hr2 : r2 = row := h_pair.2.2
  simp [hr1, hr2] at h_pair
  exact h_pair.3

theorem correctness
(lst: List (List Int))
(x: Int)
: problem_spec implementation lst x := by
  simp [problem_spec]
  use implementation lst x
  constructor
  · rfl
  · simp [implementation]
    constructor
    · intro i hi
      have h_mem : (sortByRowThenCol (findAllOccurrences lst x))[i]! ∈ sortByRowThenCol (findAllOccurrences lst x) := by
        exact List.get_mem _ i hi
      rw [sortByRowThenCol_preserves_membership] at h_mem
      rw [findAllOccurrences_correct] at h_mem
      obtain ⟨row, col⟩ := (sortByRowThenCol (findAllOccurrences lst x))[i]!
      exact h_mem
    · constructor
      · intro i j hi hj hval
        rw [sortByRowThenCol_preserves_membership]
        rw [findAllOccurrences_correct]
        exact ⟨hi, hj, hval⟩
      · constructor
        · have h_sorted := sortByRowThenCol_sorted (findAllOccurrences lst x)
          exact row_sorted_from_pairwise _ h_sorted
        · intro i hi
          obtain ⟨row, col⟩ := (sortByRowThenCol (findAllOccurrences lst x))[i]!
          simp
          have h_sorted := sortByRowThenCol_sorted (findAllOccurrences lst x)
          exact col_sorted_within_row _ row h_sorted