import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "ufunc.__call__",
  "category": "Core Method",
  "description": "Call the ufunc on the given arguments",
  "signature": "ufunc.__call__(*args, out=None, where=True, casting='same_kind', order='K', dtype=None, subok=True, signature=None, extobj=None)",
  "parameters": {
    "args": "Input arrays",
    "out": "Location(s) for the result",
    "where": "Condition to select where the operation should occur",
    "casting": "Controls what kind of data casting may occur",
    "order": "Memory layout order",
    "dtype": "Output data type",
    "subok": "If True, subclasses will be passed through",
    "signature": "Generalized ufunc signature",
    "extobj": "Buffer size, error mode, and error callback function"
  }
}
-/

/-- Apply a binary universal function elementwise to two vectors.
    This represents the core __call__ behavior for binary ufuncs like add, multiply, etc. -/
def ufunc_call {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) : Id (Vector Float n) :=
  Vector.ofFn fun i => op (a.get i) (b.get i)

/-- Specification: ufunc.__call__ applies the operation elementwise to input vectors.
    The result has the same shape as the inputs (broadcasting to common shape) and
    each element is computed by applying the operation to corresponding elements. -/
theorem ufunc_call_spec {n : Nat} (op : Float → Float → Float) (a b : Vector Float n) :
    ⦃⌜True⌝⦄
    ufunc_call op a b
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = op (a.get i) (b.get i)⌝⦄ := by
  simp only [ufunc_call, Id.run_pure, pure_triple]
  constructor
  · trivial
  · intro i
    simp [Vector.get_ofFn]