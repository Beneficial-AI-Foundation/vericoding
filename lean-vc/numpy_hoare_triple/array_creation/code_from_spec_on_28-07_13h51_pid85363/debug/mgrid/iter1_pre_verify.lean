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
def Float.toUInt64 (f : Float) : UInt64 :=
  f.toUInt64

-- LLM HELPER
lemma float_arithmetic_helper {start stop step : Float} {i : Nat} (h_step_pos : step > 0) 
    (h_range : start < stop) (h_i : i < ((stop - start) / step).toUInt64.toNat) :
    start + Float.ofNat i * step < stop := by
  have h1 : (Float.ofNat i) < (stop - start) / step := by
    rw [Float.lt_div_iff_mul_lt h_step_pos]
    rw [Float.ofNat_lt_iff]
    have h2 : i < ((stop - start) / step).toUInt64.toNat := h_i
    have h3 : Float.ofNat i < ((stop - start) / step).toUInt64.toFloat := by
      simp [Float.toUInt64]
      exact Float.ofNat_lt_of_lt_toNat h2
    exact h3
  have h2 : Float.ofNat i * step < stop - start := by
    rw [← Float.div_lt_iff_lt_mul h_step_pos]
    exact h1
  linarith

/-- Creates a 1D meshgrid from start to stop with step size.
    This is a simplified version of mgrid that handles only the single-slice case. -/
def mgrid {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) : Id (Vector Float n) :=
  let vec_data := List.range n |>.map (fun i => start + Float.ofNat i * step)
  have h_len : vec_data.length = n := by
    simp [vec_data]
    exact List.length_map _ _
  ⟨vec_data, h_len⟩

/-- Specification: mgrid creates a vector of evenly spaced values from start to stop (exclusive) with given step -/
theorem mgrid_spec {n : Nat} (start stop step : Float) (h_valid : n = ((stop - start) / step).toUInt64.toNat) 
    (h_step_pos : step > 0) (h_range : start < stop) :
    ⦃⌜step > 0 ∧ start < stop ∧ n = ((stop - start) / step).toUInt64.toNat⌝⦄
    mgrid start stop step h_valid
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = start + Float.ofNat i.val * step ∧
                 result.get i < stop⌝⦄ := by
  intro h_pre
  simp [mgrid]
  constructor
  · intro i
    constructor
    · simp [Vector.get]
      rw [List.get_map]
      simp
    · simp [Vector.get]
      rw [List.get_map]
      simp
      exact float_arithmetic_helper h_step_pos h_range (by rw [h_valid]; exact i.isLt)