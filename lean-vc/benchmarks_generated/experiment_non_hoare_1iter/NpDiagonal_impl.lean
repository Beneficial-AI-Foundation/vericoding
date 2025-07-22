/-
# NumPy Diagonal Specification

Port of np_diagonal.dfy to Lean 4
-/

-- LLM HELPER
def Matrix (m n : Nat) (α : Type) : Type := Array (Array α)

namespace DafnySpecs.NpDiagonal

-- LLM HELPER
def diagonal_length_pos (n : Nat) (k : Int) (h : k > 0) : Nat :=
  if h_pos : k.natAbs < n then n - k.natAbs else 0

-- LLM HELPER
def diagonal_length_neg (n : Nat) (k : Int) (h : k ≤ 0) : Nat :=
  if h_pos : k.natAbs < n then n - k.natAbs else 0

-- LLM HELPER
def diagonal_impl {n : Nat} (arr : Matrix n n Int) (k : Int) : List Int :=
  if k ≥ 0 then
    let offset := k.natAbs
    let len := if offset < n then n - offset else 0
    List.range len |>.map (fun i => arr[i]![i + offset]!)
  else
    let offset := k.natAbs
    let len := if offset < n then n - offset else 0
    List.range len |>.map (fun i => arr[i + offset]![i]!)

/-- Extract diagonal elements from a square matrix -/
def diagonal {n : Nat} (arr : Matrix n n Int) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n - k.natAbs) := by
  if h : k > 0 then
    let offset := k.natAbs
    let len := if offset < n then n - offset else 0
    have h_eq : len = n - k.natAbs := by
      simp [len]
      split_ifs with h_lt
      · rfl
      · simp [Int.natAbs_pos.mpr (ne_of_gt h)] at h_lt
        have : n ≤ k.natAbs := Nat.le_of_not_gt h_lt
        simp [Nat.sub_eq_zero_of_le this]
    rw [←h_eq]
    exact ⟨List.range len |>.map (fun i => arr[i]![i + offset]!), by simp⟩
  else
    let offset := k.natAbs
    let len := if offset < n then n - offset else 0
    have h_eq : len = n - k.natAbs := by
      simp [len]
      split_ifs with h_lt
      · rfl
      · have : n ≤ k.natAbs := Nat.le_of_not_gt h_lt
        simp [Nat.sub_eq_zero_of_le this]
    rw [←h_eq]
    exact ⟨List.range len |>.map (fun i => arr[i + offset]![i]!), by simp⟩

/-- Specification: The result has correct length -/
theorem diagonal_length {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n - k.natAbs := by
  simp [diagonal]
  split_ifs with h
  · simp [Vector.toList_length]
  · simp [Vector.toList_length]

/-- Specification: Elements are correctly extracted -/
theorem diagonal_spec {n : Nat} (arr : Matrix n n Int) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  ∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]! := by
  intro i hi
  simp [diagonal] at ret hi ⊢
  split_ifs with h_pos h_ge
  · simp [Vector.getElem_mk, List.getElem_map, List.getElem_range]
  · simp [Vector.getElem_mk, List.getElem_map, List.getElem_range]
  · simp [Vector.getElem_mk, List.getElem_map, List.getElem_range]
  · simp [Vector.getElem_mk, List.getElem_map, List.getElem_range]

end DafnySpecs.NpDiagonal