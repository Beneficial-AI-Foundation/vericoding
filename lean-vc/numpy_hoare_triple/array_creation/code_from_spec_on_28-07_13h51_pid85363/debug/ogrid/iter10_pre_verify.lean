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
def linspace_aux (start stop : Float) (n : Nat) (i : Nat) : Float :=
  if n ≤ 1 then start else start + i.toFloat * ((stop - start) / (n - 1).toFloat)

/-- Create a 1D open grid from start to stop with n evenly spaced points.
    This is a simplified version of ogrid that handles the common case of
    creating a single evenly-spaced vector (like ogrid[start:stop:nj]) -/
def ogrid {n : Nat} (start stop : Float) : Vector Float n :=
  Vector.ofFn (fun i => linspace_aux start stop n i.val)

/-- Specification: ogrid creates n evenly spaced points from start to stop (inclusive).
    When n > 1, the spacing between consecutive points is (stop - start) / (n - 1).
    For n = 1, the single point is at start. -/
def problem_spec {n : Nat} (impl : Float → Float → Vector Float n) (start stop : Float) : Prop :=
  n > 0 → 
  let result := impl start stop
  -- For a single element, it equals start
  (n = 1 → result.get ⟨0, by linarith⟩ = start) ∧
  -- For multiple elements, they are evenly spaced from start to stop
  (∀ i : Fin n, 
    n > 1 → result.get i = start + i.val.toFloat * ((stop - start) / (n - 1).toFloat)) ∧
  -- Boundary conditions
  (n > 1 → result.get ⟨0, by linarith⟩ = start ∧ 
           result.get ⟨n - 1, by linarith⟩ = stop)

def implementation {n : Nat} (start stop : Float) : Vector Float n :=
  Vector.ofFn (fun i => linspace_aux start stop n i.val)

-- LLM HELPER
lemma linspace_aux_n_le_1 (start stop : Float) (n : Nat) (i : Nat) :
  n ≤ 1 → linspace_aux start stop n i = start := by
  intro h
  simp [linspace_aux, h]

-- LLM HELPER
lemma linspace_aux_n_gt_1 (start stop : Float) (n : Nat) (i : Nat) :
  n > 1 → linspace_aux start stop n i = start + i.toFloat * ((stop - start) / (n - 1).toFloat) := by
  intro h
  simp [linspace_aux]
  have : ¬(n ≤ 1) := Nat.not_le.mpr h
  simp [this]

-- LLM HELPER
lemma vector_get_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  rfl

theorem correctness {n : Nat} (start stop : Float) : problem_spec (@implementation n) start stop := by
  intro h
  simp [implementation, problem_spec]
  constructor
  · intro h_n_eq_1
    rw [vector_get_ofFn]
    rw [linspace_aux_n_le_1]
    · rfl
    · rw [h_n_eq_1]
      norm_num
  constructor
  · intros i h_n_gt_1
    rw [vector_get_ofFn]
    exact linspace_aux_n_gt_1 start stop n i.val h_n_gt_1
  · intro h_n_gt_1
    constructor
    · rw [vector_get_ofFn]
      rw [linspace_aux_n_gt_1 start stop n 0 h_n_gt_1]
      simp
    · rw [vector_get_ofFn]
      rw [linspace_aux_n_gt_1 start stop n (n - 1) h_n_gt_1]
      simp
      have h_pos : (n : Float) > 0 := by
        simp
        linarith
      have h_sub_pos : (n - 1 : Float) > 0 := by
        simp
        linarith
      field_simp
      ring