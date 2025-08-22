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
instance {α : Type} {n : Nat} : GetElem (Vector α n) Nat α (fun _ i => i < n) where
  getElem v i h := v.val[i]!

-- LLM HELPER
def Vector.toList {α : Type} {n : Nat} (v : Vector α n) : List α := v.val.toList

-- LLM HELPER
instance {α : Type} {m n : Nat} : GetElem (Matrix α m n) Nat (Array α) (fun _ i => i < m) where
  getElem mat i h := mat.val[i]!

-- LLM HELPER
def Matrix.get {α : Type} {m n : Nat} (mat : Matrix α m n) (i j : Nat) (hi : i < m) (hj : j < n) : α :=
  mat.val[i]![j]!

-- LLM HELPER
def diagonal_size (n : Nat) (k : Int) : Nat :=
  if k > 0 then n - k.natAbs else n + k.natAbs

-- LLM HELPER
def fill_diagonal (arr : Matrix Int n n) (k : Int) (result : Array Int) (i : Nat) : Array Int :=
  if k ≥ 0 then
    if i < result.size ∧ i < n ∧ i + k.natAbs < n then
      result.set! i (arr.val[i]![i + k.natAbs]!)
    else result
  else
    if i < result.size ∧ i + k.natAbs < n ∧ i < n then
      result.set! i (arr.val[i + k.natAbs]![i]!)
    else result

-- LLM HELPER
def fill_diagonal_loop (arr : Matrix Int n n) (k : Int) (result : Array Int) (i : Nat) : Array Int :=
  if i >= result.size then result
  else fill_diagonal_loop arr k (fill_diagonal arr k result i) (i + 1)
termination_by result.size - i

-- LLM HELPER
lemma fill_diagonal_loop_size {n : Nat} (arr : Matrix Int n n) (k : Int) (result : Array Int) (i : Nat) :
  (fill_diagonal_loop arr k result i).size = result.size := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    simp [fill_diagonal_loop]
    split_ifs with h
    · rfl
    · have : i < result.size := Nat.not_le.mp h
      rw [ih (i + 1)]
      · simp [fill_diagonal]
        split_ifs <;> simp [Array.size_set]
      · exact Nat.succ_lt_succ_iff.mpr this

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
    if k ≥ 0 then ret[i]! = arr[i]![i + k.natAbs]!
    else ret[i]! = arr[i + k.natAbs]![i]! := by
  intro i hi
  simp [diagonal, Vector.toList] at hi ⊢
  sorry

end DafnySpecs.NpDiagonal