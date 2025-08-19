import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.tile",
  "category": "Tiling Arrays",
  "description": "Construct an array by repeating A the number of times given by reps",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.tile.html",
  "doc": "Construct an array by repeating A the number of times given by reps.\n\nIf `reps` has length ``d``, the result will have dimension of\n``max(d, A.ndim)``.\n\nIf ``A.ndim < d``, `A` is promoted to be d-dimensional by prepending new\naxes. So a shape (3,) array is promoted to (1, 3) for 2-D replication,\nor shape (1, 1, 3) for 3-D replication. If this is not the desired\nbehavior, promote `A` to d-dimensions manually before calling this\nfunction.\n\nIf ``A.ndim > d``, `reps` is promoted to `A`.ndim by prepending 1's to it.\nThus for an `A` of shape (2, 3, 4, 5), a `reps` of (2, 2) is treated as\n(1, 1, 2, 2).\n\nParameters\n----------\nA : array_like\n    The input array.\nreps : array_like\n    The number of repetitions of `A` along each axis.\n\nReturns\n-------\nc : ndarray\n    The tiled output array.\n\nExamples\n--------\n>>> a = np.array([0, 1, 2])\n>>> np.tile(a, 2)\narray([0, 1, 2, 0, 1, 2])\n>>> np.tile(a, (2, 2))\narray([[0, 1, 2, 0, 1, 2],\n       [0, 1, 2, 0, 1, 2]])\n>>> np.tile(a, (2, 1, 2))\narray([[[0, 1, 2, 0, 1, 2]],\n       [[0, 1, 2, 0, 1, 2]]])\n\n>>> b = np.array([[1, 2], [3, 4]])\n>>> np.tile(b, 2)\narray([[1, 2, 1, 2],\n       [3, 4, 3, 4]])\n>>> np.tile(b, (2, 1))\narray([[1, 2],\n       [3, 4],\n       [1, 2],\n       [3, 4]])\n\n>>> c = np.array([1,2,3,4])\n>>> np.tile(c,(4,1))\narray([[1, 2, 3, 4],\n       [1, 2, 3, 4],\n       [1, 2, 3, 4],\n       [1, 2, 3, 4]])",
  "code": "# Implementation in numpy/lib/_shape_base_impl.py\n# See NumPy source code repository",
  "source_location": "numpy/lib/_shape_base_impl.py",
  "signature": "numpy.tile(A, reps)"
}
-/

open Std.Do

/-- Constructs a vector by repeating the input vector `reps` times.
    For 1D case: tile([a, b, c], 3) = [a, b, c, a, b, c, a, b, c] -/
def tile {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) : Id (Vector α (n * reps)) :=
  Vector.mk (List.range reps |>.bind (fun _ => A.toList))

/-- Specification: tile repeats the input vector `reps` times, where each element
    at position i in the result corresponds to element at position (i % n) in the input -/
theorem tile_spec {α : Type} {n : Nat} (A : Vector α n) (reps : Nat) (h_reps : reps > 0) :
    ⦃⌜reps > 0⌝⦄
    tile A reps
    ⦃⇓result => ⌜∀ i : Fin (n * reps), result.get i = A.get ⟨i.val % n, by
      -- We need to prove i.val % n < n
      cases n with
      | zero =>
        -- If n = 0, then n * reps = 0, so there are no valid Fin (n * reps)
        simp at i
        exact absurd i.isLt (Nat.not_lt_zero _)
      | succ n' =>
        -- If n = succ n', then n > 0
        exact Nat.mod_lt i.val (Nat.zero_lt_succ n')
    ⟩⌝⦄ := by
  simp [HoareTriple]
  intro h
  simp [tile]
  intro i
  -- LLM HELPER
  have h_len : (List.range reps |>.bind (fun _ => A.toList)).length = n * reps := by
    rw [List.length_bind]
    simp [List.length_range]
    rw [List.sum_replicate, List.length_toList]
  -- LLM HELPER
  have h_get : (List.range reps |>.bind (fun _ => A.toList)).get ⟨i.val, by rw [h_len]; exact i.isLt⟩ = 
               A.toList.get ⟨i.val % n, by
                 cases n with
                 | zero =>
                   simp at i
                   exact absurd i.isLt (Nat.not_lt_zero _)
                 | succ n' =>
                   rw [List.length_toList]
                   exact Nat.mod_lt i.val (Nat.zero_lt_succ n')
               ⟩ := by
    rw [List.get_bind_range_replicate]
    exact h_reps
  rw [Vector.get_mk, h_get, List.get_toList]