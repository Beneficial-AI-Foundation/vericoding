import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.fill_diagonal",
  "category": "Diagonal operations",
  "description": "Fill the main diagonal of the given array of any dimensionality",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.fill_diagonal.html",
  "doc": "Fill the main diagonal of the given array of any dimensionality.\n\nFor an array \`a\` with \`\`a.ndim >= 2\`\`, the diagonal is the list of locations with indices \`\`a[i, ..., i]\`\` all identical. This function modifies the input array in-place, it does not return a value.\n\nParameters\n----------\na : array, at least 2-D.\n    Array whose diagonal is to be filled, it gets modified in-place.\nval : scalar or array_like\n    Value(s) to write on the diagonal. If \`val\` is scalar, the value is written along the diagonal. If array-like, the flattened \`val\` is written along the diagonal, repeating if necessary to fill all diagonal entries.\nwrap : bool\n    For tall matrices in NumPy version up to 1.6.2, the diagonal \"wrapped\" after N columns. You can have this behavior with this option. This affects only tall matrices.",
  "code": "def fill_diagonal(a, val, wrap=False):\n    \"\"\"Fill the main diagonal of the given array of any dimensionality.\n\n    For an array \`a\` with \`\`a.ndim >= 2\`\`, the diagonal is the list of\n    locations with indices \`\`a[i, ..., i]\`\` all identical. This function\n    modifies the input array in-place, it does not return a value.\n\n    Parameters\n    ----------\n    a : array, at least 2-D.\n      Array whose diagonal is to be filled in-place.\n    val : scalar or array_like\n      Value(s) to write on the diagonal.\n    wrap : bool\n      For tall matrices, control diagonal wrapping behavior.\n\n    Modifies the input array in-place without returning a value.\n    \"\"\"\n    if a.ndim < 2:\n        raise ValueError(\"array must be at least 2-d\")\n    end = None\n    if a.ndim == 2:\n        # Explicit, fast formula for the common case.  For 2-d arrays, we\n        # accept rectangular ones.\n        step = a.shape[1] + 1\n        # This is needed to don't have tall matrix have the diagonal wrap.\n        if not wrap:\n            end = a.shape[1] * a.shape[1]\n    else:\n        # For more than d=2, the strided formula is only valid for arrays with\n        # all dimensions equal, so we check first.\n        if not np.all(diff(a.shape) == 0):\n            raise ValueError(\"All dimensions of input must be of equal length\")\n        step = 1 + np.cumprod(a.shape[:-1]).sum()\n\n    # Write the value out into the diagonal.\n    a.flat[:end:step] = val"
}
-/

open Std.Do

/-- Fill the main diagonal of a 2D matrix with a specified value -/
def fill_diagonal {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) : 
    Id (Vector (Vector T cols) rows) :=
  sorry

/-- Specification: fill_diagonal modifies the diagonal entries to the specified value -/
theorem fill_diagonal_spec {T : Type} {rows cols : Nat} (mat : Vector (Vector T cols) rows) (val : T) :
    ⦃⌜True⌝⦄
    fill_diagonal mat val
    ⦃⇓result => ⌜-- Diagonal elements are filled with val
      (∀ i : Fin rows, ∀ j : Fin cols, i.val = j.val → 
        (result.get i).get j = val) ∧
      -- Non-diagonal elements remain unchanged
      (∀ i : Fin rows, ∀ j : Fin cols, i.val ≠ j.val → 
        (result.get i).get j = (mat.get i).get j)⌝⦄ := by
  sorry