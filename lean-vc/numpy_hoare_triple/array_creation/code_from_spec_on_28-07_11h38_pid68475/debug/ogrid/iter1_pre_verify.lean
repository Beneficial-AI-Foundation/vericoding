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
def computeOgridElement (start stop : Float) (n : Nat) (i : Nat) : Float :=
  if n = 1 then start
  else start + i.toFloat * ((stop - start) / (n - 1).toFloat)

/-- Create a 1D open grid from start to stop with n evenly spaced points.
    This is a simplified version of ogrid that handles the common case of
    creating a single evenly-spaced vector (like ogrid[start:stop:nj]) -/
def ogrid {n : Nat} (start stop : Float) : Id (Vector Float n) :=
  pure (Vector.ofFn (fun i => computeOgridElement start stop n i.val))

-- LLM HELPER
lemma Vector.get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get, Vector.ofFn]

-- LLM HELPER
lemma computeOgridElement_single (start stop : Float) :
  computeOgridElement start stop 1 0 = start := by
  simp [computeOgridElement]

-- LLM HELPER
lemma computeOgridElement_multiple (start stop : Float) (n : Nat) (i : Nat) (h : n > 1) :
  computeOgridElement start stop n i = start + i.toFloat * ((stop - start) / (n - 1).toFloat) := by
  simp [computeOgridElement]
  rw [if_neg]
  omega

-- LLM HELPER
lemma computeOgridElement_start (start stop : Float) (n : Nat) (h : n > 1) :
  computeOgridElement start stop n 0 = start := by
  rw [computeOgridElement_multiple start stop n 0 h]
  simp

-- LLM HELPER
lemma computeOgridElement_end (start stop : Float) (n : Nat) (h : n > 1) :
  computeOgridElement start stop n (n - 1) = stop := by
  rw [computeOgridElement_multiple start stop n (n - 1) h]
  simp [Nat.cast_sub, Nat.one_le_iff_ne_zero]
  ring_nf
  simp
  omega

/-- Specification: ogrid creates n evenly spaced points from start to stop (inclusive).
    When n > 1, the spacing between consecutive points is (stop - start) / (n - 1).
    For n = 1, the single point is at start. -/
theorem ogrid_spec {n : Nat} (start stop : Float) (h : n > 0) :
    ⦃⌜n > 0⌝⦄
    ogrid start stop
    ⦃⇓result => ⌜-- For a single element, it equals start
                (n = 1 → result.get ⟨0, h⟩ = start) ∧
                -- For multiple elements, they are evenly spaced from start to stop
                (∀ i : Fin n, 
                  n > 1 → result.get i = start + i.val.toFloat * ((stop - start) / (n - 1).toFloat)) ∧
                -- Boundary conditions
                (n > 1 → result.get ⟨0, h⟩ = start ∧ 
                         result.get ⟨n - 1, Nat.sub_lt h (Nat.zero_lt_one)⟩ = stop)⌝⦄ := by
  rw [Triple.pure_spec]
  constructor
  · exact h
  · simp [ogrid]
    constructor
    · intro h_single
      rw [Vector.get_ofFn]
      simp [h_single, computeOgridElement_single]
    · constructor
      · intros i h_multi
        rw [Vector.get_ofFn]
        exact computeOgridElement_multiple start stop n i.val h_multi
      · intro h_multi
        constructor
        · rw [Vector.get_ofFn]
          exact computeOgridElement_start start stop n h_multi
        · rw [Vector.get_ofFn]
          exact computeOgridElement_end start stop n h_multi