import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.ogrid",
  "category": "Numerical ranges",
  "description": "An instance which returns an open multi-dimensional meshgrid",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.ogrid.html",
  "doc": "\nAn instance which returns an open multi-dimensional \"meshgrid\".\n\nAn instance of numpy.lib.ndmgr.OGridClass which, when indexed, returns an open multi-dimensional meshgrid.\n\nParameters\n----------\n[slice1, slice2, ..., sliceN] : slice objects or integers\n    If the input is a slice, the syntax start:stop:step is equivalent to np.arange(start, stop, step) \n    inside of the brackets. If the input is an integer, the syntax i is equivalent to np.arange(i)+1.\n\nReturns\n-------\nout : one ndarray or tuple of ndarrays\n    If only one slice is passed, returns an array. If multiple slices are passed, returns a tuple \n    of arrays with only one non-unit dimension each.\n\nExamples\n--------\n>>> from numpy import ogrid\n>>> ogrid[-1:1:5j]\narray([-1. , -0.5,  0. ,  0.5,  1. ])\n\n>>> ogrid[0:5, 0:5]\n[array([[0],\n        [1],\n        [2],\n        [3],\n        [4]]), \n array([[0, 1, 2, 3, 4]])]\n\nNotes\n-----\nThe multi-dimensional \"mesh\" is open, which means that only one dimension of each returned \nargument is greater than 1. The output of ogrid is an open mesh of arrays that can be used \nfor broadcasting.\n",
  "code": "# numpy.ogrid is an instance of OGridClass\n# Implementation in numpy/lib/ndmgr.py\nogrid = OGridClass()\n\nclass OGridClass(nd_grid):\n    \"\"\"\n    An instance which returns an open multi-dimensional \"meshgrid\".\n    \n    An instance of \`numpy.lib.ndmgr.OGridClass\` which, when indexed, returns an\n    open (i.e. not fleshed out) mesh-grid.\n    \"\"\"\n    def __init__(self):\n        super().__init__(sparse=True)\n\n    def __getitem__(self, key):\n        # Complex implementation that handles slice notation\n        # Returns sparse/open meshgrid arrays\n        pass",
  "signature": "numpy.ogrid = <numpy.lib.ndmgr.OGridClass object>"
}
-/

-- LLM HELPER
def ogridAux (n : Nat) (start stop : Float) (i : Nat) : Float :=
  if n = 1 then start
  else start + i.toFloat * ((stop - start) / (n - 1).toFloat)

/-- Specification: ogrid creates n evenly spaced points from start to stop (inclusive).
    When n > 1, the spacing between consecutive points is (stop - start) / (n - 1).
    For n = 1, the single point is at start. -/
def problem_spec {n : Nat} (impl : Float → Float → Id (Vector Float n)) (start stop : Float) (h : n > 0) : Prop :=
    ⦃⌜n > 0⌝⦄
    impl start stop
    ⦃⇓result => ⌜-- For a single element, it equals start
                (n = 1 → result.get ⟨0, h⟩ = start) ∧
                -- For multiple elements, they are evenly spaced from start to stop
                (∀ i : Fin n, 
                  n > 1 → result.get i = start + i.val.toFloat * ((stop - start) / (n - 1).toFloat)) ∧
                -- Boundary conditions
                (n > 1 → result.get ⟨0, h⟩ = start ∧ 
                         result.get ⟨n - 1, Nat.sub_lt h (Nat.zero_lt_one)⟩ = stop)⌝⦄

/-- Create a 1D open grid from start to stop with n evenly spaced points.
    This is a simplified version of ogrid that handles the common case of
    creating a single evenly-spaced vector (like ogrid[start:stop:nj]) -/
def implementation {n : Nat} (start stop : Float) : Id (Vector Float n) :=
  Vector.ofFn (fun i => ogridAux n start stop i.val)

-- LLM HELPER
lemma ogridAux_single (start stop : Float) : ogridAux 1 start stop 0 = start := by
  simp [ogridAux]

-- LLM HELPER
lemma ogridAux_multiple (n : Nat) (start stop : Float) (i : Nat) (h : n > 1) :
    ogridAux n start stop i = start + i.toFloat * ((stop - start) / (n - 1).toFloat) := by
  simp [ogridAux, Nat.ne_of_gt h]

-- LLM HELPER
lemma ogridAux_start (n : Nat) (start stop : Float) (h : n > 1) :
    ogridAux n start stop 0 = start := by
  rw [ogridAux_multiple n start stop 0 h]
  simp

-- LLM HELPER
lemma ogridAux_end (n : Nat) (start stop : Float) (h : n > 1) :
    ogridAux n start stop (n - 1) = stop := by
  rw [ogridAux_multiple n start stop (n - 1) h]
  simp only [Nat.cast_sub, Nat.cast_one]
  have h_pos : (n : Float) > 1 := by simp [Nat.one_lt_cast.mpr h]
  field_simp
  ring

theorem correctness {n : Nat} (start stop : Float) (h : n > 0) : problem_spec implementation start stop h := by
  simp [problem_spec, implementation, Triple.hoare_pure]
  constructor
  · intro h_eq
    simp [Vector.get, Vector.ofFn, ogridAux_single]
  constructor
  · intro i h_gt
    simp [Vector.get, Vector.ofFn, ogridAux_multiple n start stop i.val h_gt]
  · intro h_gt
    constructor
    · simp [Vector.get, Vector.ofFn, ogridAux_start n start stop h_gt]
    · simp [Vector.get, Vector.ofFn, ogridAux_end n start stop h_gt]