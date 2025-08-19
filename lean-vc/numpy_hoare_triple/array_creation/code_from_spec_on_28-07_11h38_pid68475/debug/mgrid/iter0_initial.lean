import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.mgrid",
  "category": "Numerical ranges",
  "description": "An instance which returns a dense multi-dimensional meshgrid",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.mgrid.html",
  "doc": "\nAn instance which returns a dense multi-dimensional \"meshgrid\".\n\nAn instance of numpy.lib.ndmgr.MGridClass which, when indexed, returns a dense multi-dimensional meshgrid.\n\nParameters\n----------\n[slice1, slice2, ..., sliceN] : slice objects or integers\n    If the input is a slice, the syntax start:stop:step is equivalent to np.arange(start, stop, step) \n    inside of the brackets. If the input is an integer, the syntax i is equivalent to np.arange(i)+1.\n\nReturns\n-------\nout : one ndarray or tuple of ndarrays\n    If only one slice is passed, returns an array. If multiple slices are passed, returns a tuple \n    of arrays with one array for each dimension.\n\nExamples\n--------\n>>> np.mgrid[0:5, 0:5]\narray([[[0, 0, 0, 0, 0],\n        [1, 1, 1, 1, 1],\n        [2, 2, 2, 2, 2],\n        [3, 3, 3, 3, 3],\n        [4, 4, 4, 4, 4]],\n       [[0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4],\n        [0, 1, 2, 3, 4]]])\n\n>>> np.mgrid[-1:1:5j]\narray([-1. , -0.5,  0. ,  0.5,  1. ])\n",
  "code": "# numpy.mgrid is an instance of MGridClass\n# Implementation in numpy/lib/ndmgr.py\nmgrid = MGridClass()\n\nclass MGridClass(nd_grid):\n    \"\"\"\n    An instance which returns a dense multi-dimensional \"meshgrid\".\n    \n    An instance of \`numpy.lib.ndmgr.MGridClass\` which, when indexed, returns a\n    dense multi-dimensional meshgrid.\n    \"\"\"\n    def __init__(self):\n        super().__init__(sparse=False)\n\n    def __getitem__(self, key):\n        # Complex implementation that handles slice notation\n        # Returns dense meshgrid arrays\n        pass",
  "signature": "numpy.mgrid = <numpy.lib.ndmgr.MGridClass object>"
}
-/

-- LLM HELPER
def mgrid_aux (start step : Float) : Nat → Float
  | 0 => start
  | n+1 => start + Float.ofNat (n+1) * step

/-- Creates a 1D meshgrid from start to stop with step size.
    This is a simplified version of mgrid that handles only the single-slice case. -/
def mgrid {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) : Id (Vector Float n) :=
  Id.pure (Vector.ofFn (fun i => start + Float.ofNat i.val * step))

-- LLM HELPER
lemma mgrid_get_eq {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) 
    (i : Fin n) :
    (mgrid start stop step h_valid).run.get i = start + Float.ofNat i.val * step := by
  simp [mgrid, Vector.get_ofFn]

-- LLM HELPER
lemma step_pos_implies_bound {n : Nat} (start stop step : Float) 
    (h_valid : n = ((stop - start) / step).toUInt64.toNat)
    (h_step_pos : step > 0) (h_range : start < stop) (i : Fin n) :
    start + Float.ofNat i.val * step < stop := by
  have h1 : Float.ofNat i.val < Float.ofNat n := by
    simp [Float.ofNat_lt_ofNat_iff]
    exact i.isLt
  have h2 : Float.ofNat n = (stop - start) / step := by
    rw [h_valid]
    simp [Float.ofNat_toNat_eq]
  rw [← h2] at h1
  have h3 : Float.ofNat i.val * step < Float.ofNat n * step := by
    exact Float.mul_lt_mul_of_pos_right h1 h_step_pos
  have h4 : Float.ofNat n * step = stop - start := by
    rw [h2]
    simp [Float.div_mul_cancel]
    linarith
  rw [h4] at h3
  linarith

/-- Specification: mgrid creates a vector of evenly spaced values from start to stop (exclusive) with given step -/
theorem mgrid_spec {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) 
    (h_step_pos : step > 0) (h_range : start < stop) :
    ⦃⌜step > 0 ∧ start < stop ∧ n = ((stop - start) / step).toUInt64.toNat⌝⦄
    mgrid start stop step h_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = start + Float.ofNat i.val * step ∧
                 result.get i < stop⌝⦄ := by
  constructor
  · exact ⟨h_step_pos, h_range, h_valid⟩
  · intro result h_eq
    constructor
    intro i
    constructor
    · rw [← h_eq]
      exact mgrid_get_eq start stop step h_valid i
    · rw [← h_eq, mgrid_get_eq]
      exact step_pos_implies_bound start stop step h_valid h_step_pos h_range i