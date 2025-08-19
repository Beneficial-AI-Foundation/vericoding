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
  (row.enum.filter (fun (i, val) => val = x)).map (fun (i, _) => (rowIdx, i))

-- LLM HELPER
def findInRowSorted (row: List Int) (x: Int) (rowIdx: Nat) : List (Nat × Nat) :=
  let matches := (row.enum.filter (fun (i, val) => val = x)).map (fun (i, _) => (rowIdx, i))
  matches.mergeSort (fun (r1, c1) (r2, c2) => c1 ≥ c2)

def implementation (lst: List (List Int)) (x: Int) : List (Nat × Nat) :=
  let allMatches := (lst.enum.map (fun (rowIdx, row) => findInRowSorted row x rowIdx)).join
  allMatches.mergeSort (fun (r1, c1) (r2, c2) => r1 ≤ r2)

-- LLM HELPER
lemma findInRowSorted_correct (row: List Int) (x: Int) (rowIdx: Nat) :
  let result := findInRowSorted row x rowIdx
  (∀ (i, j) ∈ result, i = rowIdx ∧ j < row.length ∧ row[j]! = x) ∧
  (∀ j < row.length, row[j]! = x → (rowIdx, j) ∈ result) := by
  simp [findInRowSorted, findInRow]
  constructor
  · intro (i, j) h
    simp at h
    obtain ⟨k, hk, heq⟩ := h
    simp at heq
    constructor
    · exact heq.1
    · constructor
      · simp [List.enum] at hk
        exact hk.1
      · simp [List.enum] at hk
        exact hk.2
  · intro j hj_bound hj_val
    simp
    use j
    constructor
    · exact ⟨hj_bound, hj_val⟩
    · simp

-- LLM HELPER
lemma implementation_finds_all (lst: List (List Int)) (x: Int) (i: Nat) (j: Nat) :
  i < lst.length → j < lst[i]!.length → (lst[i]!)[j]! = x → (i, j) ∈ implementation lst x := by
  intro hi hj hval
  simp [implementation]
  use i, hi, (i, j)
  constructor
  · simp [findInRowSorted, findInRow]
    use j
    simp [List.enum]
    exact ⟨hj, hval⟩
  · simp

-- LLM HELPER
lemma implementation_only_finds_valid (lst: List (List Int)) (x: Int) :
  ∀ (i, j) ∈ implementation lst x, i < lst.length ∧ j < lst[i]!.length ∧ (lst[i]!)[j]! = x := by
  intro (i, j) h
  simp [implementation] at h
  obtain ⟨k, hk, pair, hpair, heq⟩ := h
  simp at heq
  rw [← heq]
  simp [findInRowSorted, findInRow] at hpair
  obtain ⟨idx, hidx, hpair_eq⟩ := hpair
  simp at hpair_eq
  simp [List.enum] at hidx
  exact ⟨hk, hidx.1, hidx.2⟩

-- LLM HELPER
lemma implementation_sorted_rows (lst: List (List Int)) (x: Int) :
  (implementation lst x).map (fun (r, c) => r) |>.Sorted Nat.le := by
  simp [implementation]
  apply List.Sorted.map
  apply List.mergeSort_sorted
  exact fun _ _ => decidable_le _ _

-- LLM HELPER
lemma implementation_sorted_cols (lst: List (List Int)) (x: Int) :
  ∀ i < (implementation lst x).length,
    let (row, col) := (implementation lst x)[i]!
    ((implementation lst x).filter (fun (r, c) => r = row)).map (fun (r, c) => c) |>.Sorted (fun a b => a ≥ b) := by
  intro i hi
  simp [implementation]
  have h : ∀ row, ((lst.enum.map (fun (rowIdx, row) => findInRowSorted row x rowIdx)).join.mergeSort (fun (r1, c1) (r2, c2) => r1 ≤ r2)).filter (fun (r, c) => r = row) = 
    (lst.enum.map (fun (rowIdx, row) => findInRowSorted row x rowIdx)).join.filter (fun (r, c) => r = row) := by
    intro row
    apply List.filter_mergeSort_comm
  simp [h]
  apply List.Sorted.map
  apply List.Sorted.filter
  simp [List.join_sorted]
  intro k hk
  simp [findInRowSorted]
  apply List.mergeSort_sorted
  exact fun _ _ => decidable_ge _ _

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
      exact implementation_only_finds_valid lst x (implementation lst x)[i]! (by simp; exact ⟨i, hi, rfl⟩)
    · constructor
      · intro i hi j hj hval
        exact implementation_finds_all lst x i j hi hj hval
      · constructor
        · exact implementation_sorted_rows lst x
        · exact implementation_sorted_cols lst x