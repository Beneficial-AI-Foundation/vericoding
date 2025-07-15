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
def findInRow (row: List Int) (x: Int) (rowIdx: Nat) : List (Nat × Nat) :=
  (row.enum.filter (fun (_, val) => val = x)).map (fun (colIdx, _) => (rowIdx, colIdx))

-- LLM HELPER
def findAllOccurrences (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  (lst.enum.map (fun (rowIdx, row) => findInRow row x rowIdx)).join

-- LLM HELPER
def sortResult (positions: List (Nat × Nat)) : List (Nat × Nat) :=
  let grouped := positions.groupBy (fun (r1, _) (r2, _) => r1 = r2)
  let sortedGroups := grouped.map (fun group => 
    group.mergeSort (fun (_, c1) (_, c2) => c1 ≥ c2))
  (sortedGroups.mergeSort (fun g1 g2 => 
    match g1.head?, g2.head? with
    | some (r1, _), some (r2, _) => r1 ≤ r2
    | _, _ => true)).join

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) := 
  sortResult (findAllOccurrences lst x)

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
    simp [List.mem_join, List.mem_map, List.mem_enum] at h
    obtain ⟨⟨ri, row⟩, ⟨hmem, hin⟩⟩ := h
    simp [List.mem_enum] at hmem
    rw [findInRow_correct] at hin
    exact ⟨hmem.1, hin.1, by rw [←hmem.2]; exact hin.2⟩
  · intro ⟨hrow, hcol, hval⟩
    simp [List.mem_join, List.mem_map, List.mem_enum]
    use (rowIdx, lst[rowIdx]!)
    constructor
    · simp [List.mem_enum]
      exact ⟨hrow, rfl⟩
    · rw [findInRow_correct]
      exact ⟨hcol, hval⟩

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
      simp [sortResult]
      sorry -- The sorting preserves the validity of positions
    · constructor
      · intro i hi j hj hval
        simp [sortResult]
        sorry -- The sorting preserves all found positions
      · constructor
        · simp [sortResult]
          sorry -- The result is sorted by row
        · intro i hi
          simp [sortResult]
          sorry -- Within each row, columns are sorted in descending order