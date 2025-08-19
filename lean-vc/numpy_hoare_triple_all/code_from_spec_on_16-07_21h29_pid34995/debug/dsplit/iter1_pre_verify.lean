import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.dsplit",
  "category": "Splitting Arrays",
  "description": "Split array into multiple sub-arrays along the 3rd axis (depth)",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.dsplit.html",
  "doc": "Split array into multiple sub-arrays along the 3rd axis (depth).\n\nPlease refer to the `split` documentation. `dsplit` is equivalent\nto `split` with ``axis=2``, the array is always split along the third\naxis provided the array dimension is greater than or equal to 3.\n\nExamples\n--------\n>>> x = np.arange(16.0).reshape(2, 2, 4)\n>>> x\narray([[[ 0.,  1.,  2.,  3.],\n        [ 4.,  5.,  6.,  7.]],\n       [[ 8.,  9., 10., 11.],\n        [12., 13., 14., 15.]]])\n>>> np.dsplit(x, 2)\n[array([[[ 0.,  1.],\n        [ 4.,  5.]],\n       [[ 8.,  9.],\n        [12., 13.]]]),\n array([[[ 2.,  3.],\n        [ 6.,  7.]],\n       [[10., 11.],\n        [14., 15.]]])]\n>>> np.dsplit(x, np.array([3, 6]))\n[array([[[ 0.,  1.,  2.],\n        [ 4.,  5.,  6.]],\n       [[ 8.,  9., 10.],\n        [12., 13., 14.]]]),\n array([[[ 3.],\n        [ 7.]],\n       [[11.],\n        [15.]]]),\n array([], shape=(2, 2, 0), dtype=float64)]",
  "code": "# Implementation in numpy/lib/_shape_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.dsplit(ary, indices_or_sections)"
}
-/

open Std.Do

-- LLM HELPER
def splitVectorHelper {n k : Nat} (arr : Vector Float (k * n)) (i : Nat) : Vector Float n :=
  Vector.ofFn (fun j => arr.get ⟨i * n + j.val, by
    have h1 : i < k := by
      have : i * n + j.val < k * n := by
        exact (⟨i * n + j.val, by omega⟩ : Fin (k * n)).isLt
      omega
    have h2 : j.val < n := j.isLt
    omega
  ⟩)

/-- Split a 1D vector into equal sections (simplified version of dsplit).
    
    Since dsplit operates on the 3rd axis of 3D arrays, this simplified version
    demonstrates the splitting behavior on a 1D vector. The actual dsplit would
    work on nested Vector structures representing 3D arrays.
    
    This function divides a vector into k equal sections, where k must divide
    the length of the vector evenly. Returns a list of vectors.
-/
def dsplit {n k : Nat} (arr : Vector Float (k * n)) (sections : Nat) 
  (h : sections = k ∧ k > 0) : Id (List (Vector Float n)) :=
  pure (List.range k |>.map (splitVectorHelper arr))

-- LLM HELPER
lemma list_length_range_map {α : Type*} (f : Nat → α) (k : Nat) : 
  (List.range k |>.map f).length = k :=
  List.length_map _ _

-- LLM HELPER
lemma get_splitVectorHelper {n k : Nat} (arr : Vector Float (k * n)) (i : Nat) (hi : i < k) (j : Fin n) :
  (splitVectorHelper arr i).get j = arr.get ⟨i * n + j.val, by
    have h2 : j.val < n := j.isLt
    omega
  ⟩ := by
  simp [splitVectorHelper, Vector.get_ofFn]

-- LLM HELPER
lemma mem_range_map {α : Type*} (f : Nat → α) (k : Nat) (x : α) :
  x ∈ (List.range k |>.map f) ↔ ∃ i : Nat, i < k ∧ f i = x := by
  simp [List.mem_map, List.mem_range]

/-- Specification: dsplit divides a vector into equal sections.
    
    Precondition: sections = k and k > 0 (array size must be k * n)
    Postcondition: Returns k sub-vectors, each of size n. The i-th sub-vector
                   contains elements from positions i*n to (i+1)*n-1 of the 
                   original array.
    
    Mathematical property: Concatenating all sub-vectors in order reconstructs
                          the original vector.
-/
theorem dsplit_spec {n k : Nat} (arr : Vector Float (k * n))
  (h : k > 0) :
  ⦃⌜k > 0⌝⦄
  dsplit arr k ⟨rfl, h⟩
  ⦃⇓result => ⌜result.length = k ∧
              ∀ i : Fin k, ∃ sub ∈ result,
                ∀ j : Fin n, sub.get j = arr.get ⟨i.val * n + j.val, by
                  have h1 : i.val < k := i.isLt
                  have h2 : j.val < n := j.isLt
                  calc i.val * n + j.val
                    < i.val * n + n := Nat.add_lt_add_left h2 _
                    _ = (i.val + 1) * n := by rw [Nat.add_mul, Nat.one_mul]
                    _ ≤ k * n := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h1)
                ⟩⌝⦄ := by
  triple_intro h
  simp [dsplit]
  constructor
  · exact list_length_range_map (splitVectorHelper arr) k
  · intro i
    use splitVectorHelper arr i.val
    constructor
    · rw [mem_range_map]
      use i.val
      exact ⟨i.isLt, rfl⟩
    · intro j
      exact get_splitVectorHelper arr i.val i.isLt j