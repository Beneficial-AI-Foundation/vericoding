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
def floatToInt (f : Float) : Int :=
  f.floor

-- LLM HELPER  
lemma float_arithmetic_helper (start stop step : Float) (i : Nat) 
    (h_step_pos : step > 0) (h_range : start < stop) 
    (h_i : i < Int.natAbs (floatToInt ((stop - start) / step))) :
    start + Float.ofNat i * step < stop := by
  have h1 : (stop - start) / step > 0 := by
    apply div_pos
    · linarith
    · exact h_step_pos
  have h2 : Float.ofNat i < (stop - start) / step := by
    rw [← Float.ofInt_natCast]
    apply Float.ofInt_lt_ofInt.mpr
    rw [Int.natCast_lt]
    rw [← Int.natAbs_of_nonneg]
    · exact h_i
    · apply Int.floor_nonneg
      exact le_of_lt h1
  rw [← add_lt_iff_sub_lt]
  rw [← div_lt_iff h_step_pos]
  exact h2

def problem_spec (mgrid_impl : ∀ (n : Nat), Float → Float → Float → (n = Int.natAbs (floatToInt ((stop - start) / step))) → Id (Array Float)) 
    (n : Nat) (start stop step : Float) (h_valid : n = Int.natAbs (floatToInt ((stop - start) / step))) 
    (h_step_pos : step > 0) (h_range : start < stop) : Prop :=
    ⦃⌜step > 0 ∧ start < stop ∧ n = Int.natAbs (floatToInt ((stop - start) / step))⌝⦄
    mgrid_impl n start stop step h_valid
    ⦃⇓result => ⌜result.size = n ∧ ∀ i : Fin n, result[i]! = start + Float.ofNat i.val * step ∧
                 result[i]! < stop⌝⦄

/-- Creates a 1D meshgrid from start to stop with step size.
    This is a simplified version of mgrid that handles only the single-slice case. -/
def mgrid (n : Nat) (start stop step : Float) (h_valid : n = Int.natAbs (floatToInt ((stop - start) / step))) : Id (Array Float) :=
  Id.run do
    let vec_data := List.map (fun i => start + Float.ofNat i * step) (List.range n)
    return vec_data.toArray

/-- Specification: mgrid creates a vector of evenly spaced values from start to stop (exclusive) with given step -/
theorem correctness (n : Nat) (start stop step : Float) (h_valid : n = Int.natAbs (floatToInt ((stop - start) / step))) 
    (h_step_pos : step > 0) (h_range : start < stop) :
    problem_spec mgrid n start stop step h_valid h_step_pos h_range := by
  unfold problem_spec
  intro h_pre
  unfold mgrid
  simp [Id.run]
  constructor
  · rw [List.size_toArray, List.length_map, List.length_range]
  · intro i
    constructor
    · simp [List.getElem_toArray, List.getElem_map, List.getElem_range]
    · simp [List.getElem_toArray, List.getElem_map, List.getElem_range]
      apply float_arithmetic_helper
      · exact h_step_pos
      · exact h_range
      · rw [h_valid]; exact i.isLt