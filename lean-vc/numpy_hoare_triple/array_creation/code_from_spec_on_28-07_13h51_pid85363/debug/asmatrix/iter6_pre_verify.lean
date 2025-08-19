import Std.Do.Triple
import Std.Tactic.Do

"name": "numpy.asmatrix",
"category": "From existing data",
"description": "Interpret the input as a matrix",
"url": "https://numpy.org/doc/stable/reference/generated/numpy.asmatrix.html",
"doc": "\nInterpret the input as a matrix.\n\nParameters\n----------\ndata : array_like\n    Input data.\ndtype : data-type\n    Data-type of the output matrix.\n\nReturns\n-------\nmat : matrix\n    data interpreted as a matrix.\n\nExamples\n--------\n>>> x = np.array([[1, 2], [3, 4]])\n\n>>> m = np.asmatrix(x)\n\n>>> x[0,0] = 5\n\n>>> m\nmatrix([[5, 2],\n        [3, 4]])\n\nNotes\n-----\nUnlike matrix, asmatrix does not make a copy if the input is already a matrix or an ndarray. \nEquivalent to matrix(data, copy=False).\n",
"code": "def asmatrix(data, dtype=None):\n    \"\"\"\n    Interpret the input as a matrix.\n\n    Unlike `matrix`, `asmatrix` does not make a copy if the input is already\n    a matrix or an ndarray.  Equivalent to ``matrix(data, copy=False)``.\n    \"\"\"\n    return matrix(data, dtype=dtype, copy=False)",
"signature": "numpy.asmatrix(data, dtype=None)"
-/

open Std.Do

def problem_spec {n : Nat} (f : Vector Float n → Id (Vector Float n)) (data : Vector Float n) : Prop :=
  ⦃⌜True⌝⦄
  f data
  ⦃⇓result => ⌜∀ i : Fin n, result.get i = data.get i⌝⦄

def implementation {n : Nat} (data : Vector Float n) : Id (Vector Float n) :=
  pure data

-- LLM HELPER
lemma pure_hoare_triple_helper {n : Nat} (data : Vector Float n) :
    ⦃⌜True⌝⦄
    pure data
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = data.get i⌝⦄ := by
  simp [Std.Do.pure_hoare_triple]
  intro h i
  rfl

theorem correctness {n : Nat} (data : Vector Float n) :
    problem_spec implementation data := 
  pure_hoare_triple_helper data