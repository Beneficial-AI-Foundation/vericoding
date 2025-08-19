/-!
{
  "name": "numpy.diagflat",
  "category": "Diagonal operations",
  "description": "Create a two-dimensional array with the flattened input as a diagonal",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.diagflat.html",
  "doc": "Create a two-dimensional array with the flattened input as a diagonal.\n\nParameters\n----------\nv : array_like\n    Input data, which is flattened and set as the \`k\`-th diagonal of the output.\nk : int, optional\n    Diagonal to set; 0, the default, corresponds to the \"main\" diagonal.\n\nReturns\n-------\nout : ndarray\n    The 2-D output array.",
  "code": "@array_function_dispatch(_diag_dispatcher)\ndef diagflat(v, k=0):\n    \"\"\"\n    Create a two-dimensional array with the flattened input as a diagonal.\n\n    Parameters\n    ----------\n    v : array_like\n        Input data, which is flattened and set as the \`k\`-th\n        diagonal of the output.\n    k : int, optional\n        Diagonal to set; 0, the default, corresponds to the \"main\" diagonal.\n\n    Returns\n    -------\n    out : ndarray\n        The 2-D output array.\n    \"\"\"\n    try:\n        wrap = v.__array_wrap__\n    except AttributeError:\n        wrap = None\n    v = asarray(v).ravel()\n    s = len(v)\n    n = s + abs(k)\n    res = zeros((n, n), v.dtype)\n    if (k >= 0):\n        i = arange(0, n - k, dtype=intp)\n        fi = i + k + i * n\n    else:\n        i = arange(0, n + k, dtype=intp)\n        fi = i + (i - k) * n\n    res.flat[fi] = v\n    if wrap:\n        return wrap(res)\n    return res"
}
-/

-- LLM HELPER
def create_diagonal_row {n : Nat} (row_idx : Fin n) (v : Vector Float n) : Vector Float n :=
  Vector.ofFn (fun col_idx => if row_idx = col_idx then v.get row_idx else 0)

/-- numpy.diagflat: Create a two-dimensional array with the flattened input as a diagonal.

    Creates a square matrix where the input vector is placed along the main diagonal.
    All other elements are zero. The resulting matrix has size n×n where n is the
    length of the input vector.
    
    For the main diagonal (k=0), the matrix element at position (i,i) contains
    the i-th element of the input vector.
-/
def diagflat {n : Nat} (v : Vector Float n) : Vector (Vector Float n) n :=
  Vector.ofFn (fun i => create_diagonal_row i v)

-- LLM HELPER
theorem create_diagonal_row_spec {n : Nat} (row_idx : Fin n) (v : Vector Float n) :
    ∀ col_idx : Fin n,
      (create_diagonal_row row_idx v).get col_idx = 
      (if row_idx = col_idx then v.get row_idx else 0) := by
  intro col_idx
  simp [create_diagonal_row]

/-- Specification: diagflat returns a square matrix where the input vector forms the main diagonal.

    Properties:
    1. The result is a square n×n matrix
    2. For all i, j: if i = j then result[i][j] = v[i] (diagonal elements)
    3. For all i, j: if i ≠ j then result[i][j] = 0 (off-diagonal elements are zero)
-/
theorem diagflat_spec {n : Nat} (v : Vector Float n) :
    let result := diagflat v
    ∀ i : Fin n, ∀ j : Fin n,
      (i = j → (result.get i).get j = v.get i) ∧
      (i ≠ j → (result.get i).get j = 0) := by
  intro i j
  simp [diagflat]
  rw [create_diagonal_row_spec]
  constructor
  · intro h
    simp [h]
  · intro h
    simp [h]