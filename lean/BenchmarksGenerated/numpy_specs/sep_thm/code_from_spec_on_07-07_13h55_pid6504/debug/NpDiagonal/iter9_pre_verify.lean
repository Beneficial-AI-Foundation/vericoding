/-
# NumPy Diagonal Specification

Port of np_diagonal.dfy to Lean 4
-/

namespace DafnySpecs.NpDiagonal

-- LLM HELPER
def Matrix (α : Type) (m n : Nat) : Type := 
  { arr : Array (Array α) // arr.size = m ∧ ∀ i, i < arr.size → arr[i]!.size = n }

-- LLM HELPER
def Vector (α : Type) (n : Nat) : Type := 
  { arr : Array α // arr.size = n }

-- LLM HELPER
instance [Inhabited α] {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i _ := v.val[i]!

-- LLM HELPER
def Vector.toList {α : Type} {n : Nat} (v : Vector α n) : List α := v.val.toList

-- LLM HELPER
instance [Inhabited α] {m n : Nat} : GetElem (Matrix α m n) Nat (Array α) (fun _ i => i < m) where
  getElem mat i _ := mat.val[i]!

-- LLM HELPER
def Matrix.get [Inhabited α] {m n : Nat} (mat : Matrix α m n) (i j : Nat) (_ : i < m) (_ : j < n) : α :=
  mat.val[i]![j]!

-- LLM HELPER
def diagonal_size (n : Nat) (k : Int) : Nat :=
  if k > 0 then n - k.natAbs else n + k.natAbs

-- LLM HELPER
def fill_diagonal (arr : Matrix Int n n) (k : Int) (result : Array Int) (idx : Nat) : Array Int :=
  if k ≥ 0 then
    if idx < result.size ∧ idx < n ∧ idx + k.natAbs < n then
      result.set! idx (arr.val[idx]![idx + k.natAbs]!)
    else result
  else
    if idx < result.size ∧ idx + k.natAbs < n ∧ idx < n then
      result.set! idx (arr.val[idx + k.natAbs]![idx]!)
    else result

-- LLM HELPER
def fill_diagonal_loop (arr : Matrix Int n n) (k : Int) (result : Array Int) (idx : Nat) : Array Int :=
  if idx >= result.size then result
  else fill_diagonal_loop arr k (fill_diagonal arr k result idx) (idx + 1)
termination_by result.size - idx

-- LLM HELPER
lemma fill_diagonal_loop_size {n : Nat} (arr : Matrix Int n n) (k : Int) (result : Array Int) (idx : Nat) :
  (fill_diagonal_loop arr k result idx).size = result.size := by
  induction idx using Nat.strong_induction_on with
  | ind idx ih =>
    simp [fill_diagonal_loop]
    split_ifs with h
    · rfl
    · have : idx < result.size := Nat.not_le.mp h
      rw [ih (idx + 1)]
      · simp [fill_diagonal]
        split_ifs <;> simp [Array.size_set]
      · exact Nat.succ_lt_succ_iff.mpr this

-- LLM HELPER
lemma Array.toList_length {α : Type} (arr : Array α) : arr.toList.length = arr.size := by
  rw [Array.toList_eq]
  simp [Array.data_length]

/-- Extract diagonal elements from a square matrix -/
def diagonal {n : Nat} (arr : Matrix Int n n) (k : Int) : Vector Int (if k > 0 then n - k.natAbs else n + k.natAbs) := 
  let size := if k > 0 then n - k.natAbs else n + k.natAbs
  let result := Array.replicate size 0
  let filled := fill_diagonal_loop arr k result 0
  ⟨filled, by 
    rw [fill_diagonal_loop_size]
    exact Array.size_replicate size 0⟩

/-- Specification: The result has correct length -/
theorem diagonal_length {n : Nat} (arr : Matrix Int n n) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  if k > 0 then ret.toList.length = n - k.natAbs else ret.toList.length = n + k.natAbs := by
  simp [diagonal, Vector.toList]
  rw [Array.toList_length, fill_diagonal_loop_size, Array.size_replicate]
  split <;> rfl

/-- Specification: Elements are correctly extracted -/
theorem diagonal_spec {n : Nat} (arr : Matrix Int n n) (k : Int)
  (h1 : -n < k ∧ k < n) :
  let ret := diagonal arr k
  ∀ i : Nat, i < ret.toList.length →
    if k ≥ 0 then ret[i] = arr[i]![i + k.natAbs]!
    else ret[i] = arr[i + k.natAbs]![i]! := by
  intro i hi
  simp [diagonal, Vector.toList] at hi ⊢
  have h_size : i < (if k > 0 then n - k.natAbs else n + k.natAbs) := by
    rw [Array.toList_length, fill_diagonal_loop_size, Array.size_replicate] at hi
    exact hi
  have h_size2 : i < (if k > 0 then n - k.natAbs else n + k.natAbs) := by
    rw [Array.toList_length, fill_diagonal_loop_size, Array.size_replicate] at hi
    exact hi
  split_ifs
  · rfl
  · rfl

end DafnySpecs.NpDiagonal