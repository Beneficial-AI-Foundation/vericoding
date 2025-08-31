/- 
{
  "name": "numpy.mgrid",
  "category": "Numerical ranges",
  "description": "An instance which returns a dense multi-dimensional meshgrid",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.mgrid.html",
  "doc": "\nAn instance which returns a dense multi-dimensional \"meshgrid\".\n\nAn instance of numpy.lib.ndmgr.MGridClass which, when indexed, returns a dense multi-dimensional meshgrid.\n\nParameters\n----------\n[slice1, slice2, ..., sliceN] : slice objects or integers\n    If the input is a slice, the syntax start:stop:step is equivalent to np.arange(start, stop, step) \n    inside of the brackets. If the input is an integer, the syntax i is equivalent to np.arange(i)+1.\n\nReturns\n-------\nout : one ndarray or tuple of ndarrays\n    If only one slice is passed, returns an array. If multiple slices are passed, returns a tuple \n    of arrays with one array for each dimension.\n\nExamples\n--------\n>>> np.mgrid[0:5, 0:5]\narray([[[0, 0, 0, 0, 0],\n        [1, 1, 1, 1, 1],\n        [2, 2, 2, 2, 2],\n        [3, 3, 3, 3, 3],\n        [4, 4, 4, 4, 4]],\n       [[0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4]]])\n\n>>> np.mgrid[-1:1:5j]\narray([-1. , -0.5,  0. ,  0.5,  1. ])\n",
  "signature": "numpy.mgrid = <numpy.lib.ndmgr.MGridClass object>"
}
-/

/-  Creates a 1D meshgrid from start to stop with step size.
    This is a simplified version of mgrid that handles only the single-slice case. -/

/-  Specification: mgrid creates a vector of evenly spaced values from start to stop (exclusive) with given step -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def mgrid {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) : Id (Vector Float n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem mgrid_spec {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) 
    (h_step_pos : step > 0) (h_range : start < stop) :
    ⦃⌜step > 0 ∧ start < stop ∧ n = ((stop - start) / step).toUInt64.toNat⌝⦄
    mgrid start stop step h_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = start + Float.ofNat i.val * step ∧
                 result.get i < stop⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
