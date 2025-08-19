import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.diag",
  "category": "Building matrices",
  "description": "Extract a diagonal or construct a diagonal array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diag.html",
  "doc": "
Extract a diagonal or construct a diagonal array.

Parameters
----------
v : array_like
    If v is a 2-D array, return a copy of its k-th diagonal. If v is a 1-D array, 
    return a 2-D array with v on the k-th diagonal.
k : int, optional
    Diagonal in question. The default is 0. Use k>0 for diagonals above the main diagonal, 
    and k<0 for diagonals below the main diagonal.

Returns
-------
out : ndarray
    The extracted diagonal or constructed diagonal array.

Examples
--------
>>> x = np.arange(9).reshape((3,3))
>>> x
array([[0, 1, 2],
       [3, 4, 5],
       [6, 7, 8]])
>>> np.diag(x)
array([0, 4, 8])
>>> np.diag(x, k=1)
array([1, 5])
>>> np.diag(x, k=-1)
array([3, 7])

>>> np.diag(np.diag(x))
array([[0, 0, 0],
       [0, 4, 0],
       [0, 0, 8]])
",
  "code": "@array_function_dispatch(_diag_dispatcher)\ndef diag(v, k=0):\n    \"\"\"\n    Extract a diagonal or construct a diagonal array.\n\n    See the more detailed documentation for ``numpy.diagonal`` if you use this\n    function to extract a diagonal and wish to write to the resulting array;\n    whether it returns a copy or a view depends on what version of numpy you\n    are using.\n    \"\"\"\n    v = asanyarray(v)\n    s = v.shape\n    if len(s) == 1:\n        n = s[0]+abs(k)\n        res = zeros((n, n), v.dtype)\n        if k >= 0:\n            i = k\n        else:\n            i = (-k) * n\n        res[:n-k].flat[i::n+1] = v\n        return res\n    elif len(s) == 2:\n        return diagonal(v, k)\n    else:\n        raise ValueError(\"Input must be 1- or 2-d.\")",
  "signature": "numpy.diag(v, k=0)"
}
-/

-- LLM HELPER
def make_row {n : Nat} (v : Vector Float n) (i : Fin n) : Vector Float n :=
  Vector.ofFn (fun j => if i = j then v.get i else 0)

def diag {n : Nat} (v : Vector Float n) : Id (Vector (Vector Float n) n) :=
  return (Vector.ofFn (make_row v))

-- LLM HELPER
lemma make_row_diagonal {n : Nat} (v : Vector Float n) (i : Fin n) :
  (make_row v i).get i = v.get i := by
  simp [make_row, Vector.get_ofFn]

-- LLM HELPER
lemma make_row_off_diagonal {n : Nat} (v : Vector Float n) (i j : Fin n) (h : i ≠ j) :
  (make_row v i).get j = 0 := by
  simp [make_row, Vector.get_ofFn, h]

-- LLM HELPER
lemma diag_get {n : Nat} (v : Vector Float n) (i : Fin n) :
  (diag v).run.get i = make_row v i := by
  simp [diag, Vector.get_ofFn, Id.run]

-- LLM HELPER
lemma sum_make_row {n : Nat} (v : Vector Float n) (i : Fin n) :
  List.sum (List.map (fun j => (make_row v i).get j) (List.finRange n)) = v.get i := by
  rw [List.sum_finRange_eq]
  simp [make_row, Vector.get_ofFn]
  rw [Finset.sum_ite_eq]
  simp

-- LLM HELPER
lemma List.sum_finRange_eq {α : Type*} [AddCommMonoid α] {n : Nat} (f : Fin n → α) :
  List.sum (List.map f (List.finRange n)) = Finset.sum Finset.univ f := by
  simp [List.finRange, List.sum_map_range]

/-- Specification: diag constructs a square matrix with v on the main diagonal.
    
    This captures the mathematical property that numpy.diag(v) creates a matrix M
    where M[i,i] = v[i] for all i, and M[i,j] = 0 for all i ≠ j.
    
    The result is an n×n matrix where:
    - The main diagonal contains the elements of the input vector v
    - All off-diagonal elements are zero
    - This represents the canonical way to construct a diagonal matrix
    
    Mathematical properties verified:
    1. Diagonal elements equality: M[i,i] = v[i]
    2. Off-diagonal zeros: M[i,j] = 0 for i ≠ j
    3. Diagonal matrix property: non-zero elements only on diagonal
    4. Trace property: tr(M) = sum(v)
    5. Symmetry: M is a symmetric matrix
    6. Idempotence property: diag(diag(M)) reconstructs M for diagonal matrices
    7. Zero count: exactly n elements are non-zero (assuming v has no zeros)
-/
def problem_spec {n : Nat} (f : Vector Float n → Id (Vector (Vector Float n) n)) (v : Vector Float n) : Prop :=
    ⦃⌜True⌝⦄
    f v
    ⦃⇓result => ⌜
      -- 1. Elements on the main diagonal are from v
      (∀ i : Fin n, (result.get i).get i = v.get i) ∧
      
      -- 2. All off-diagonal elements are zero
      (∀ i j : Fin n, i ≠ j → (result.get i).get j = 0) ∧
      
      -- 3. Sanity check: diagonal matrix property - non-zero elements only on diagonal
      (∀ i j : Fin n, (result.get i).get j ≠ 0 → i = j) ∧
      
      -- 4. Matrix trace equals sum of input vector elements
      (List.sum (List.map (fun i => (result.get i).get i) (List.finRange n)) = 
       List.sum (List.map (fun i => v.get i) (List.finRange n))) ∧
      
      -- 5. The resulting matrix is symmetric
      (∀ i j : Fin n, (result.get i).get j = (result.get j).get i) ∧
      
      -- 6. Row and column sums: for each row/column, sum equals the corresponding diagonal element
      (∀ i : Fin n, 
        List.sum (List.map (fun j => (result.get i).get j) (List.finRange n)) = v.get i) ∧
      (∀ j : Fin n,
        List.sum (List.map (fun i => (result.get i).get j) (List.finRange n)) = v.get j) ∧
        
      -- 7. Determinant property: det(diag(v)) = product of diagonal elements
      -- (This is a fundamental property of diagonal matrices, though we don't compute it here)
      
      -- 8. Each row has exactly one non-zero element at position i (unless v[i] = 0)
      (∀ i : Fin n, v.get i ≠ 0 → 
        ((result.get i).get i ≠ 0 ∧ ∀ j : Fin n, j ≠ i → (result.get i).get j = 0)) ∧
      
      -- 9. Each column has exactly one non-zero element at position j (unless v[j] = 0)
      (∀ j : Fin n, v.get j ≠ 0 → 
        ((result.get j).get j ≠ 0 ∧ ∀ i : Fin n, i ≠ j → (result.get i).get j = 0))
    ⌝⦄

theorem correctness {n : Nat} (v : Vector Float n) : problem_spec diag v := by
  unfold problem_spec
  apply wp_return.mpr
  simp only [diag, Id.run]
  repeat' constructor
  · -- Property 1: diagonal elements
    intro i
    rw [Vector.get_ofFn, make_row_diagonal]
  · -- Property 2: off-diagonal elements are zero
    intro i j h
    rw [Vector.get_ofFn, make_row_off_diagonal _ _ _ h]
  · -- Property 3: diagonal matrix property
    intro i j h
    rw [Vector.get_ofFn] at h
    simp [make_row, Vector.get_ofFn] at h
    by_cases hij : i = j
    · exact hij
    · simp [hij] at h
  · -- Property 4: trace equals sum
    simp [List.map_map]
    congr 1
    ext i
    rw [Vector.get_ofFn, make_row_diagonal]
  · -- Property 5: symmetry
    intro i j
    rw [Vector.get_ofFn, Vector.get_ofFn]
    simp [make_row, Vector.get_ofFn]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, hij.symm]
  · -- Property 6a: row sums
    intro i
    rw [Vector.get_ofFn]
    exact sum_make_row v i
  · -- Property 6b: column sums
    intro j
    rw [List.sum_finRange_eq]
    simp [Vector.get_ofFn, make_row, Vector.get_ofFn]
    rw [Finset.sum_ite_eq]
    simp
  · -- Property 8: row non-zero structure
    intro i h
    constructor
    · rw [Vector.get_ofFn, make_row_diagonal]
      exact h
    · intro j hj
      rw [Vector.get_ofFn, make_row_off_diagonal _ _ _ hj]
  · -- Property 9: column non-zero structure
    intro j h
    constructor
    · rw [Vector.get_ofFn, make_row_diagonal]
      exact h
    · intro i hi
      rw [Vector.get_ofFn, make_row_off_diagonal _ _ _ hi.symm]