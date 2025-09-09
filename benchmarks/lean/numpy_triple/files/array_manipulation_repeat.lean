/- 
{
  "name": "numpy.repeat",
  "category": "Tiling Arrays",
  "description": "Repeat elements of an array",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.repeat.html",
  "doc": "Repeat elements of an array.\n\nParameters\n----------\na : array_like\n    Input array.\nrepeats : int or array of ints\n    The number of repetitions for each element. \`repeats\` is broadcasted\n    to fit the shape of the given axis.\naxis : int, optional\n    The axis along which to repeat values. By default, use the\n    flattened input array, and return a flat output array.\n\nReturns\n-------\nrepeated_array : ndarray\n    Output array which has the same shape as \`a\`, except along\n    the given axis.\n\nExamples\n--------\n>>> np.repeat(3, 4)\narray([3, 3, 3, 3])\n>>> x = np.array([[1,2],[3,4]])\n>>> np.repeat(x, 2)\narray([1, 1, 2, 2, 3, 3, 4, 4])\n>>> np.repeat(x, 3, axis=1)\narray([[1, 1, 1, 2, 2, 2],\n       [3, 3, 3, 4, 4, 4]])\n>>> np.repeat(x, [1, 2], axis=0)\narray([[1, 2],\n       [3, 4],\n       [3, 4]])",
  "source_location": "numpy/_core/fromnumeric.py",
  "signature": "numpy.repeat(a, repeats, axis=None)"
}
-/

/-  Repeat elements of a vector a specified number of times.
    Each element is repeated consecutively. -/

/-  Specification: repeat creates a vector where each element from the input 
    appears consecutively 'repeats' times. The resulting vector has size n * repeats.

    For a vector [a₀, a₁, ..., aₙ₋₁] and repeats = r, the result is:
    [a₀, a₀, ..., a₀, a₁, a₁, ..., a₁, ..., aₙ₋₁, aₙ₋₁, ..., aₙ₋₁]
     \___r times___/  \___r times___/       \______r times______/

    Mathematical properties:
    1. Each element appears exactly 'repeats' times consecutively
    2. The total size is n * repeats
    3. Element at index i comes from input element at index ⌊i/repeats⌋
    4. Elements are grouped: positions [k*repeats, (k+1)*repeats) contain a[k]
-/

import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def «repeat» {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) : Id (Vector α (n * repeats)) :=
  sorry

theorem repeat_spec {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) (h_pos : repeats > 0) :
    ⦃⌜repeats > 0⌝⦄
    «repeat» a repeats
    ⦃⇓result => ⌜(∀ i : Fin (n * repeats), 
                   ∃ (k : Fin n), 
                     i.val / repeats = k.val ∧ 
                     result.get i = a.get k) ∧
                  (∀ k : Fin n, ∀ j : Fin repeats,
                   ∃ (idx : Fin (n * repeats)),
                     idx.val = k.val * repeats + j.val ∧
                     result.get idx = a.get k)⌝⦄ := by
  sorry
