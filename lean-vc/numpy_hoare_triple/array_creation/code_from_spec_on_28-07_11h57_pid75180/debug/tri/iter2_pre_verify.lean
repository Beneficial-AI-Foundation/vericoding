import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.tri",
  "category": "Building matrices",
  "description": "An array with ones at and below the given diagonal and zeros elsewhere",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tri.html",
  "doc": "\nAn array with ones at and below the given diagonal and zeros elsewhere.\n\nParameters\n----------\nN : int\n    Number of rows in the array.\nM : int, optional\n    Number of columns in the array. By default, M is taken equal to N.\nk : int, optional\n    The sub-diagonal at and below which the array is filled. k = 0 is the main diagonal, \n    while k < 0 is below it, and k > 0 is above. The default is 0.\ndtype : dtype, optional\n    Data type of the returned array. The default is float.\nlike : array_like, optional\n    Reference object to allow the creation of arrays which are not NumPy arrays.\n\nReturns\n-------\ntri : ndarray of shape (N, M)\n    Array with its lower triangle filled with ones and zero elsewhere; in other words \n    T[i,j] == 1 for j <= i + k, 0 otherwise.\n\nExamples\n--------\n>>> np.tri(3, 5, 2, dtype=int)\narray([[1, 1, 1, 0, 0],\n       [1, 1, 1, 1, 0],\n       [1, 1, 1, 1, 1]])\n\n>>> np.tri(3, 5, -1)\narray([[0.,  0.,  0.,  0.,  0.],\n       [1.,  0.,  0.,  0.,  0.],\n       [1.,  1.,  0.,  0.,  0.]])\n",
  "code": "@set_array_function_like_doc\n@set_module('numpy')\ndef tri(N, M=None, k=0, dtype=float, *, like=None):\n    \"\"\"\n    An array with ones at and below the given diagonal and zeros elsewhere.\n    \"\"\"\n    if like is not None:\n        return _tri_with_like(like, N, M=M, k=k, dtype=dtype)\n\n    if M is None:\n        M = N\n\n    m = greater_equal.outer(arange(N, dtype=_nx.intp),\n                            arange(-k, M-k, dtype=_nx.intp))\n\n    # Avoid making a copy if the requested type is already bool\n    m = m.astype(dtype, copy=False)\n\n    return m",
  "signature": "numpy.tri(N, M=None, k=0, dtype=<class 'float'>, *, like=None)"
}
-/

-- LLM HELPER
def create_row (i : Nat) (M : Nat) (k : Int) : Vector Float M :=
  Vector.ofFn (fun j => if (j.val : Int) ≤ (i : Int) + k then 1.0 else 0.0)

/-- An array with ones at and below the given diagonal and zeros elsewhere.
    
    Creates a matrix of shape (N, M) where T[i,j] = 1 if j ≤ i + k, and 0 otherwise.
    The parameter k controls the diagonal: k = 0 is the main diagonal,
    k < 0 is below it, and k > 0 is above it.
-/
def tri (N M : Nat) (k : Int) : Id (Vector (Vector Float M) N) :=
  Id.pure (Vector.ofFn (fun i => create_row i.val M k))

-- LLM HELPER
lemma create_row_get (i : Nat) (M : Nat) (k : Int) (j : Fin M) :
    (create_row i M k).get j = if (j.val : Int) ≤ (i : Int) + k then 1.0 else 0.0 := by
  unfold create_row
  simp [Vector.get, Vector.ofFn]

/-- Specification: tri creates a lower triangular matrix with specified diagonal offset.
    
    The resulting matrix has ones at and below the k-th diagonal, zeros elsewhere.
    For each position (i, j):
    - If j ≤ i + k, then the value is 1.0
    - Otherwise, the value is 0.0
    
    This captures the mathematical property that defines a generalized lower triangular matrix.
-/
theorem tri_spec (N M : Nat) (k : Int) :
    ⦃⌜True⌝⦄
    tri N M k
    ⦃⇓result => ⌜∀ (i : Fin N) (j : Fin M), 
                  (result.get i).get j = if (j.val : Int) ≤ (i.val : Int) + k then 1.0 else 0.0⌝⦄ := by
  simp [tri, Id.spec, Id.pure]
  intro i j
  simp [Vector.get, Vector.ofFn]
  exact create_row_get i.val M k j