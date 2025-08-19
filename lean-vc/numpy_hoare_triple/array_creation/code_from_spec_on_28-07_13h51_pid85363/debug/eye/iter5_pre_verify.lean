import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.eye",
  "category": "From shape or value",
  "description": "Return a 2-D array with ones on the diagonal and zeros elsewhere",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.eye.html",
  "doc": "\nReturn a 2-D array with ones on the diagonal and zeros elsewhere.\n\nParameters\n----------\nN : int\n    Number of rows in the output.\nM : int, optional\n    Number of columns in the output. If None, defaults to N.\nk : int, optional\n    Index of the diagonal: 0 (the default) refers to the main diagonal, \n    a positive value refers to an upper diagonal, and a negative value to a lower diagonal.\ndtype : data-type, optional\n    Data-type of the returned array.\norder : {'C', 'F'}, optional\n    Whether the output should be stored in row-major (C-style) or column-major (Fortran-style) order in memory.\n\nReturns\n-------\nI : ndarray of shape (N,M)\n    An array where all elements are equal to zero, except for the k-th diagonal, whose values are equal to one.\n\nExamples\n--------\n>>> np.eye(2, dtype=int)\narray([[1, 0],\n       [0, 1]])\n>>> np.eye(3, k=1)\narray([[0.,  1.,  0.],\n       [0.,  0.,  1.],\n       [0.,  0.,  0.]])\n",
  "code": "@set_array_function_like_doc\n@set_module('numpy')\ndef eye(N, M=None, k=0, dtype=float, order='C', *, device=None, like=None):\n    \"\"\"\n    Return a 2-D array with ones on the diagonal and zeros elsewhere.\n    \"\"\"\n    if like is not None:\n        return _eye_with_like(like, N, M=M, k=k, dtype=dtype, order=order,\n                             device=device)\n    if M is None:\n        M = N\n    m = zeros((N, M), dtype=dtype, order=order, device=device)\n    if k >= M:\n        return m\n    M = M if k >= 0 else M + k\n    N = N if k <= 0 else N - k\n    m[:min(N, M)-max(0, -k), max(0, -k):].flat[::M + 1] = 1\n    return m",
  "signature": "numpy.eye(N, M=None, k=0, dtype=<class 'float'>, order='C', *, device=None, like=None)"
}
-/

-- LLM HELPER
def makeRow (n : Nat) (i : Fin n) : Vector Float n :=
  Vector.ofFn (fun j => if i = j then 1.0 else 0.0)

def eye {n : Nat} : Id (Vector (Vector Float n) n) :=
  pure (Vector.ofFn (makeRow n))

/-- Specification: eye returns a square identity matrix with mathematical properties.
    
    Precondition: True (no special preconditions for identity matrix creation)
    
    Postcondition: The returned matrix satisfies:
    1. Main diagonal elements are 1.0
    2. Off-diagonal elements are 0.0
    3. The matrix is square (n x n)
    4. Mathematical properties:
       - Symmetry: eye[i][j] = eye[j][i]
       - Uniqueness: There is exactly one 1.0 in each row and column
       - Matrix multiplication identity: For any compatible matrix A, eye * A = A
    
    This captures the complete mathematical characterization of an identity matrix.
-/
def problem_spec {n : Nat} : 
    ((Vector (Vector Float n) n) → Prop) → Id (Vector (Vector Float n) n) → Prop :=
  fun Q ma => 
    ⦃⌜True⌝⦄
    ma
    ⦃fun result => ⌜
      -- Basic structure: diagonal ones, off-diagonal zeros
      (∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = if i = j then 1.0 else 0.0) ∧
      -- Symmetry property (identity matrices are symmetric)
      (∀ i : Fin n, ∀ j : Fin n, 
        (result.get i).get j = (result.get j).get i) ∧
      -- Uniqueness property: exactly one 1.0 in each row
      (∀ i : Fin n, ∃ j : Fin n, (result.get i).get j = 1.0 ∧ 
        ∀ k : Fin n, (result.get i).get k = 1.0 → k = j) ∧
      -- Uniqueness property: exactly one 1.0 in each column
      (∀ j : Fin n, ∃ i : Fin n, (result.get i).get j = 1.0 ∧ 
        ∀ k : Fin n, (result.get k).get j = 1.0 → k = i) ∧
      -- All non-diagonal elements are exactly 0.0
      (∀ i : Fin n, ∀ j : Fin n, i ≠ j → (result.get i).get j = 0.0)
    ⌝⦄ ∧ Q result

theorem correctness {n : Nat} : problem_spec (fun _ => True) (@eye n) := by
  simp [problem_spec, eye, makeRow, htpy_pure]
  constructor
  · intro i j
    simp [Vector.get_ofFn]
  constructor
  · intro i j
    simp [Vector.get_ofFn]
    by_cases h : i = j <;> simp [h]
  constructor
  · intro i
    use i
    constructor
    · simp [Vector.get_ofFn]
    · intro k hk
      simp [Vector.get_ofFn] at hk
      by_cases h : i = k
      · exact h
      · simp [h] at hk
  constructor
  · intro j
    use j
    constructor
    · simp [Vector.get_ofFn]
    · intro k hk
      simp [Vector.get_ofFn] at hk
      by_cases h : k = j
      · exact h.symm
      · simp [h] at hk
  · intro i j hij
    simp [Vector.get_ofFn, hij]