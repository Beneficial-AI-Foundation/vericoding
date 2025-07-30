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
  (result.map (fun (r, c) => r)).Sorted Nat.le ∧
  (∀ i, i < result.length →
    let (row, col) := result[i]!
    ((result.filter (fun (r, c) => r = row)).map (fun (r, c) => c)).Sorted (fun a b => a ≥ b))
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
    simp [List.mem_map, List.mem_filter, List.mem_enum] at h
    obtain ⟨⟨ci, val⟩, ⟨hfilter, heq⟩⟩ := h
    simp at heq
    rw [←heq.2]
    simp [List.mem_filter, List.mem_enum] at hfilter
    exact ⟨hfilter.1.1, hfilter.2⟩
  · intro ⟨hlen, hval⟩
    simp [List.mem_map, List.mem_filter, List.mem_enum]
    use (colIdx, row[colIdx]!)
    constructor
    · simp [List.mem_filter, List.mem_enum]
      exact ⟨⟨hlen, rfl⟩, hval⟩
    · simp

-- LLM HELPER
lemma findAllOccurrences_correct (lst: List (List Int)) (x: Int) :
  ∀ (rowIdx colIdx: Nat), (rowIdx, colIdx) ∈ findAllOccurrences lst x ↔ 
  (rowIdx < lst.length ∧ colIdx < lst[rowIdx]!.length ∧ (lst[rowIdx]!)[colIdx]! = x) := by
  intro rowIdx colIdx
  simp [findAllOccurrences]
  constructor
  · intro h
    simp [List.mem_flatten, List.mem_map, List.mem_enum] at h
    obtain ⟨⟨ri, row⟩, ⟨hmem, hin⟩⟩ := h
    simp [List.mem_enum] at hmem
    rw [findInRow_correct] at hin
    exact ⟨hmem.1, hin.1, by rw [←hmem.2]; exact hin.2⟩
  · intro ⟨hrow, hcol, hval⟩
    simp [List.mem_flatten, List.mem_map, List.mem_enum]
    use (rowIdx, lst[rowIdx]!)
    constructor
    · simp [List.mem_enum]
      exact ⟨hrow, rfl⟩
    · rw [findInRow_correct]
      exact ⟨hcol, hval⟩

-- LLM HELPER
lemma sortByRowThenCol_preserves_membership (positions: List (Nat × Nat)) :
  ∀ p, p ∈ sortByRowThenCol positions ↔ p ∈ positions := by
  intro p
  simp [sortByRowThenCol]
  exact List.mem_mergeSort

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
      have h_mem : (implementation lst x)[i]! ∈ implementation lst x := by
        simp [List.get_mem]
      simp [implementation] at h_mem
      rw [sortByRowThenCol_preserves_membership] at h_mem
      rw [findAllOccurrences_correct] at h_mem
      obtain ⟨row, col⟩ := (sortByRowThenCol (findAllOccurrences lst x))[i]!
      exact h_mem
    · constructor
      · intro i j hi hj hval
        simp [implementation]
        rw [sortByRowThenCol_preserves_membership]
        rw [findAllOccurrences_correct]
        exact ⟨hi, hj, hval⟩
      · constructor
        · simp [implementation, sortByRowThenCol]
          apply List.Sorted.map
          apply List.Sorted.mergeSort
          intro a b c hab hbc
          simp at hab hbc
          by_cases h1 : a.1 = b.1
          · by_cases h2 : b.1 = c.1
            · simp [h1, h2]
            · simp [h1, h2] at hab hbc
              exact Nat.le_trans hab hbc
          · simp [h1] at hab
            by_cases h2 : b.1 = c.1
            · simp [h2] at hbc
              exact Nat.le_trans hab hbc
            · simp [h2] at hbc
              exact Nat.le_trans hab hbc
        · intro i hi
          simp [implementation, sortByRowThenCol]
          apply List.Sorted.filter
          apply List.Sorted.map
          apply List.Sorted.mergeSort
          intro a b c hab hbc
          obtain ⟨row, col⟩ := (sortByRowThenCol (findAllOccurrences lst x))[i]!
          simp at hab hbc
          by_cases h1 : a.1 = b.1
          · by_cases h2 : b.1 = c.1
            · simp [h1, h2] at hab hbc
              exact Nat.le_trans hbc hab
            · simp [h1, h2] at hab hbc
              exact Nat.le_refl _
          · simp [h1] at hab
            by_cases h2 : b.1 = c.1
            · simp [h2] at hbc
              exact Nat.le_refl _
            · simp [h2] at hbc
              exact Nat.le_refl _