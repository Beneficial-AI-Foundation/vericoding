import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.bmat",
  "category": "Building matrices",
  "description": "Build a matrix object from a string, nested sequence, or array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.bmat.html",
  "doc": "\nBuild a matrix object from a string, nested sequence, or array.\n\nParameters\n----------\nobj : str or array_like\n    Input data. If a string, variables in the current scope may be referenced by name.\nldict : dict, optional\n    A dictionary that replaces local operands in current frame. Ignored if obj is not a string or gdict is None.\ngdict : dict, optional\n    A dictionary that replaces global operands in current frame. Ignored if obj is not a string.\n\nReturns\n-------\nout : matrix\n    Returns a matrix object, which is a specialized 2-D array.\n\nExamples\n--------\n>>> A = np.asmatrix('1 1; 1 1')\n>>> B = np.asmatrix('2 2; 2 2')\n>>> C = np.asmatrix('3 4; 5 6')\n>>> D = np.asmatrix('7 8; 9 0')\n\nBuild a block matrix from nested lists:\n>>> np.bmat([[A, B], [C, D]])\nmatrix([[1, 1, 2, 2],\n        [1, 1, 2, 2],\n        [3, 4, 7, 8],\n        [5, 6, 9, 0]])\n\n>>> np.bmat(np.r_[np.c_[A, B], np.c_[C, D]])\nmatrix([[1, 1, 2, 2],\n        [1, 1, 2, 2],\n        [3, 4, 7, 8],\n        [5, 6, 9, 0]])\n\n>>> np.bmat('A,B; C,D')\nmatrix([[1, 1, 2, 2],\n        [1, 1, 2, 2],\n        [3, 4, 7, 8],\n        [5, 6, 9, 0]])\n\nSee Also\n--------\nnumpy.block : A generalization of this function for N-d arrays, that returns normal ndarrays.\n\nNotes\n-----\nAll the input arrays must have the same number of dimensions, but row and column sizes only need to be compatible. \n",
  "code": "@set_module('numpy')\ndef bmat(obj, ldict=None, gdict=None):\n    \"\"\"\n    Build a matrix object from a string, nested sequence, or array.\n    \"\"\"\n    if isinstance(obj, str):\n        if gdict is None:\n            # get previous frame\n            frame = sys._getframe().f_back\n            glob_dict = frame.f_globals\n            loc_dict = frame.f_locals\n        else:\n            glob_dict = gdict\n            loc_dict = ldict\n\n        return matrix(_from_string(obj, glob_dict, loc_dict))\n\n    if isinstance(obj, (tuple, list)):\n        # [[A,B],[C,D]]\n        arr_rows = []\n        for row in obj:\n            if isinstance(row, ndarray):  # not 2-d\n                return matrix(concatenate(obj, axis=-1))\n            else:\n                arr_rows.append(concatenate(row, axis=-1))\n        return matrix(concatenate(arr_rows, axis=0))\n\n    if isinstance(obj, ndarray):\n        return matrix(obj)\n\n    return matrix(obj)",
  "signature": "numpy.bmat(obj, ldict=None, gdict=None)"
}
-/

-- LLM HELPER
def Vector.append {α : Type} {n m : Nat} (v1 : Vector α n) (v2 : Vector α m) : Vector α (n + m) :=
  ⟨v1.toArray ++ v2.toArray, by simp [Array.size_append]⟩

-- LLM HELPER
lemma add_assoc_helper (n : Nat) : n + n + n + n = 4 * n := by
  ring

/-- Build a matrix from a 2x2 block structure using 4 input vectors.
    This represents a simplified version of numpy.bmat for 2x2 block matrices.
    The result is a flattened vector representing the block matrix in row-major order.
    
    Mathematically, this constructs a 2x2 block matrix where each block is a 1×n vector:
    [ topLeft    | topRight    ]
    [ bottomLeft | bottomRight ]
    
    The result is flattened as [topLeft | topRight | bottomLeft | bottomRight].
-/
def bmat {n : Nat} (topLeft topRight bottomLeft bottomRight : Vector Float n) : Id (Vector Float (4 * n)) :=
  pure ⟨((topLeft.append topRight).append bottomLeft).append bottomRight |>.toArray, by
    simp [Vector.append]
    rw [add_assoc_helper]⟩

-- LLM HELPER
theorem pure_triple (α : Type) (x : α) (P : α → Prop) : P x → ⦃⌜True⌝⦄ pure x ⦃⇓result => ⌜P result⌝⦄ := by
  intro h
  constructor
  · simp
  · exact h

/-- Specification: bmat constructs a 2x2 block matrix from four equal-sized vectors.
    The result is a flattened vector where blocks are arranged as:
    [topLeft | topRight | bottomLeft | bottomRight]
    This captures the essential behavior of numpy.bmat for block matrix construction.
    
    Precondition: True (no special preconditions for basic block matrix construction)
    Postcondition: Each block is correctly placed in the flattened result
-/
theorem bmat_spec {n : Nat} (topLeft topRight bottomLeft bottomRight : Vector Float n) :
    ⦃⌜True⌝⦄
    bmat topLeft topRight bottomLeft bottomRight
    ⦃⇓result => ⌜(∀ i : Fin n, result.get ⟨i.val, by omega⟩ = topLeft.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + n, by omega⟩ = topRight.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + 2*n, by omega⟩ = bottomLeft.get i) ∧
                 (∀ i : Fin n, result.get ⟨i.val + 3*n, by omega⟩ = bottomRight.get i)⌝⦄ := by
  unfold bmat
  apply pure_triple
  constructor
  · intro i
    simp [Vector.append, Vector.get]
  · constructor
    · intro i
      simp [Vector.append, Vector.get]
    · constructor
      · intro i
        simp [Vector.append, Vector.get]
      · intro i
        simp [Vector.append, Vector.get]