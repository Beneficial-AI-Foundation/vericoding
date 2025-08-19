import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.squeeze",
  "category": "Changing Dimensions",
  "description": "Remove axes of length one from a",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.squeeze.html",
  "doc": "Remove axes of length one from \`a\`.\n\nParameters\n----------\na : array_like\n    Input data.\naxis : None or int or tuple of ints, optional\n    Selects a subset of the entries of length one in the\n    shape. If an axis is selected with shape entry greater than\n    one, an error is raised.\n\nReturns\n-------\nsqueezed : ndarray\n    The input array, but with all or a subset of the\n    dimensions of length 1 removed. This is always \`a\` itself\n    or a view into \`a\`. Note that if all axes are squeezed,\n    the result is a 0d array and not a scalar.\n\nExamples\n--------\n>>> x = np.array([[[0], [1], [2]]])\n>>> x.shape\n(1, 3, 1)\n>>> np.squeeze(x).shape\n(3,)\n>>> np.squeeze(x, axis=0).shape\n(3, 1)\n>>> np.squeeze(x, axis=1).shape\nTraceback (most recent call last):\n...\nValueError: cannot select an axis to squeeze out which has size not equal to one\n>>> np.squeeze(x, axis=2).shape\n(1, 3)\n>>> x = np.array([[1234]])\n>>> x.shape\n(1, 1)\n>>> np.squeeze(x)\narray(1234)  # 0d array\n>>> np.squeeze(x).shape\n()\n>>> np.squeeze(x)[()]\n1234",
  "code": "@array_function_dispatch(_squeeze_dispatcher)\ndef squeeze(a, axis=None):\n    \"\"\"Remove axes of length one from \`a\`.\"\"\"\n    try:\n        squeeze = a.squeeze\n    except AttributeError:\n        return _wrapit(a, 'squeeze', axis=axis)\n    if axis is None:\n        return squeeze()\n    else:\n        return squeeze(axis=axis)",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.squeeze(a, axis=None)"
}
-/

open Std.Do

/-- Squeeze a single-element vector to extract its value.
    This is a simplified 1D version of numpy.squeeze for vectors of size 1. -/
def squeeze {α : Type} (a : Vector α 1) : Id α :=
  return a.get ⟨0, by decide⟩

-- LLM HELPER
theorem fin_one_unique : ∀ i : Fin 1, i = ⟨0, by decide⟩ := by
  intro i
  fin_cases i
  rfl

/-- Specification: squeeze extracts the single element from a size-1 vector.
    
    Mathematical properties:
    1. The result equals the first (and only) element of the input vector
    2. For any function f, squeeze preserves function application: f(squeeze(a)) = f(a[0])
    3. squeeze is the inverse of creating a single-element vector
    
    Sanity checks:
    - The input must be a vector of exactly size 1
    - The output type changes from Vector to the element type
    - This models numpy's behavior where squeeze([x]) returns x as a 0D array -/
theorem squeeze_spec {α : Type} (a : Vector α 1) :
    ⦃⌜True⌝⦄
    squeeze a
    ⦃⇓result => ⌜result = a.get ⟨0, by decide⟩ ∧ 
                 -- Mathematical property: squeeze is injective
                 (∀ b : Vector α 1, squeeze a = squeeze b → a = b) ∧
                 -- Mathematical property: squeeze preserves function application
                 (∀ (β : Type) (f : α → β), f result = f (a.get ⟨0, by decide⟩)) ∧
                 -- Sanity check: result is the unique element in the vector
                 (∀ i : Fin 1, a.get i = result)⌝⦄ := by
  simp [squeeze]
  constructor
  · rfl
  constructor
  · intro b h
    ext i
    have h1 : a.get ⟨0, by decide⟩ = b.get ⟨0, by decide⟩ := h
    rw [fin_one_unique i]
    exact h1
  constructor
  · intro β f
    rfl
  · intro i
    rw [fin_one_unique i]