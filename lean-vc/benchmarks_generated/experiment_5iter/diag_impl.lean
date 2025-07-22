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
def makeRow {n : Nat} (v : Vector Float n) (i : Fin n) : Vector Float n :=
  Vector.ofFn fun j => if i = j then v.get i else 0

/-- Construct a diagonal matrix from a 1-D vector -/
def diag {n : Nat} (v : Vector Float n) : Id (Vector (Vector Float n) n) :=
  pure (Vector.ofFn (makeRow v))

-- LLM HELPER
lemma makeRow_diagonal {n : Nat} (v : Vector Float n) (i : Fin n) : 
  (makeRow v i).get i = v.get i := by
  simp [makeRow, Vector.get_ofFn]

-- LLM HELPER
lemma makeRow_off_diagonal {n : Nat} (v : Vector Float n) (i j : Fin n) (h : i ≠ j) : 
  (makeRow v i).get j = 0 := by
  simp [makeRow, Vector.get_ofFn, h]

-- LLM HELPER
lemma diag_get {n : Nat} (v : Vector Float n) (i : Fin n) : 
  (diag v).run.get i = makeRow v i := by
  simp [diag, Vector.get_ofFn]

-- LLM HELPER
lemma makeRow_sum {n : Nat} (v : Vector Float n) (i : Fin n) :
  List.sum (List.map (fun j => (makeRow v i).get j) (List.finRange n)) = v.get i := by
  have h : List.sum (List.map (fun j => (makeRow v i).get j) (List.finRange n)) = 
           List.sum (List.map (fun j => if i = j then v.get i else 0) (List.finRange n)) := by
    congr 1
    congr 1
    ext j
    simp [makeRow, Vector.get_ofFn]
  rw [h]
  have : List.sum (List.map (fun j => if i = j then v.get i else 0) (List.finRange n)) = v.get i := by
    rw [List.sum_map_ite, List.filter_finRange_eq]
    simp
  exact this

-- LLM HELPER
lemma column_sum {n : Nat} (v : Vector Float n) (j : Fin n) :
  List.sum (List.map (fun i => (diag v).run.get i.get j) (List.finRange n)) = v.get j := by
  have h : List.sum (List.map (fun i => (diag v).run.get i.get j) (List.finRange n)) = 
           List.sum (List.map (fun i => if i = j then v.get i else 0) (List.finRange n)) := by
    congr 1
    congr 1
    ext i
    rw [diag_get, makeRow]
    simp [Vector.get_ofFn]
  rw [h]
  have : List.sum (List.map (fun i => if i = j then v.get i else 0) (List.finRange n)) = v.get j := by
    rw [List.sum_map_ite, List.filter_finRange_eq]
    simp
  exact this

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
theorem diag_spec {n : Nat} (v : Vector Float n) :
    ⦃⌜True⌝⦄
    diag v
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
    ⌝⦄ := by
  simp [wpSpec_pure, diag]
  constructor
  · -- 1. Diagonal elements
    intro i
    rw [Vector.get_ofFn, makeRow_diagonal]
  constructor
  · -- 2. Off-diagonal zeros
    intro i j h
    rw [Vector.get_ofFn, makeRow_off_diagonal _ _ _ h]
  constructor
  · -- 3. Diagonal matrix property
    intro i j h
    rw [Vector.get_ofFn] at h
    simp [makeRow, Vector.get_ofFn] at h
    by_contra h_neq
    simp [h_neq] at h
  constructor
  · -- 4. Trace property
    congr 1
    ext i
    rw [Vector.get_ofFn, makeRow_diagonal]
  constructor
  · -- 5. Symmetry
    intro i j
    rw [Vector.get_ofFn, Vector.get_ofFn]
    simp [makeRow, Vector.get_ofFn]
    by_cases h : i = j
    · simp [h]
    · simp [h, h.symm]
  constructor
  · -- 6a. Row sums
    intro i
    rw [Vector.get_ofFn]
    exact makeRow_sum v i
  constructor
  · -- 6b. Column sums
    intro j
    have h : List.sum (List.map (fun i => (Vector.ofFn (makeRow v)).get i.get j) (List.finRange n)) = 
             List.sum (List.map (fun i => (makeRow v i).get j) (List.finRange n)) := by
      congr 1
      congr 1
      ext i
      rw [Vector.get_ofFn]
    rw [h]
    rw [List.sum_map_ite, List.filter_finRange_eq]
    simp [makeRow, Vector.get_ofFn]
  constructor
  · -- 8. Row non-zero property
    intro i h
    constructor
    · rw [Vector.get_ofFn, makeRow_diagonal]
      exact h
    · intro j h_neq
      rw [Vector.get_ofFn, makeRow_off_diagonal _ _ _ h_neq]
  · -- 9. Column non-zero property
    intro j h
    constructor
    · rw [Vector.get_ofFn, makeRow_diagonal]
      exact h
    · intro i h_neq
      rw [Vector.get_ofFn, makeRow_off_diagonal _ _ _ h_neq.symm]