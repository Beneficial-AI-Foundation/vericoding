import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.zeros_like",
  "category": "From shape or value",
  "description": "Return an array of zeros with the same shape and type as a given array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.zeros_like.html",
  "doc": "\nReturn an array of zeros with the same shape and type as a given array.\n\nParameters\n----------\na : array_like\n    The shape and data-type of a define these same attributes of the returned array.\ndtype : data-type, optional\n    Overrides the data type of the result.\norder : {'C', 'F', 'A', or 'K'}, optional\n    Overrides the memory layout of the result.\nsubok : bool, optional\n    If True, then the newly created array will use the sub-class type of a, otherwise it will be a base-class array.\nshape : int or sequence of ints, optional\n    Overrides the shape of the result.\n\nReturns\n-------\nout : ndarray\n    Array of zeros with the same shape and type as a.\n\nExamples\n--------\n>>> x = np.arange(6)\n>>> x = x.reshape((2, 3))\n>>> x\narray([[0, 1, 2],\n       [3, 4, 5]])\n>>> np.zeros_like(x)\narray([[0, 0, 0],\n       [0, 0, 0]])\n",
  "code": "@array_function_dispatch(_zeros_like_dispatcher)\ndef zeros_like(\n    a, dtype=None, order='K', subok=True, shape=None, *, device=None\n):\n    \"\"\"\n    Return an array of zeros with the same shape and type as a given array.\n    \"\"\"\n    res = empty_like(\n        a, dtype=dtype, order=order, subok=subok, shape=shape, device=device\n    )\n    # needed instead of a 0 to get same result as zeros for string dtypes\n    z = zeros(1, dtype=res.dtype)\n    multiarray.copyto(res, z, casting='unsafe')\n    return res",
  "signature": "numpy.zeros_like(a, dtype=None, order='K', subok=True, shape=None, *, device=None)"
}
-/

open Std.Do

/-- Return a vector of zeros with the same length as the input vector.
    This is the 1D version of numpy.zeros_like which creates a new vector
    filled with zeros, having the same size as the input vector. -/
def zeros_like {n : Nat} {T : Type} [Zero T] (a : Vector T n) : Id (Vector T n) :=
  pure (Vector.mk (Array.replicate n 0) (by simp [Array.size_replicate]))

-- LLM HELPER
lemma Array.getElem_replicate (n : Nat) (v : T) (i : Fin n) :
  (Array.replicate n v)[i] = v := by
  simp [Array.getElem_replicate]

-- LLM HELPER
lemma Vector.get_mk_replicate {n : Nat} {T : Type} (v : T) (i : Fin n) :
  (Vector.mk (Array.replicate n v) (by simp [Array.size_replicate])).get i = v := by
  simp [Vector.get, Array.getElem_replicate]

-- LLM HELPER
lemma zero_add {T : Type} [Add T] [Zero T] [AddZeroClass T] (v : T) : 0 + v = v := by
  exact zero_add v

-- LLM HELPER
lemma add_zero {T : Type} [Add T] [Zero T] [AddZeroClass T] (v : T) : v + 0 = v := by
  exact add_zero v

/-- Specification: zeros_like returns a vector where every element is 0,
    with the same length as the input vector.
    
    Mathematical properties:
    1. The result has the same length as the input (enforced by type system)
    2. Every element in the result is exactly 0
    3. The result is independent of the input values (only depends on shape)
    4. The result is the additive identity for vector addition
    5. For numeric types, the sum of all elements is zero -/
theorem zeros_like_spec {n : Nat} {T : Type} [Zero T] [Add T] [AddZeroClass T] (a : Vector T n) :
    ⦃⌜True⌝⦄
    zeros_like a
    ⦃fun result => ⌜(∀ i : Fin n, result.get i = 0) ∧
                 (∀ v : Vector T n, ∀ i : Fin n, 
                   (result.get i + v.get i = v.get i) ∧ 
                   (v.get i + result.get i = v.get i))⌝⦄ := by
  simp [zeros_like, DoNotation.bind, DoNotation.pure, Id.bind, Id.pure]
  constructor
  · intro i
    simp [Vector.get_mk_replicate]
  · intro v i
    constructor
    · simp [Vector.get_mk_replicate, zero_add]
    · simp [Vector.get_mk_replicate, add_zero]