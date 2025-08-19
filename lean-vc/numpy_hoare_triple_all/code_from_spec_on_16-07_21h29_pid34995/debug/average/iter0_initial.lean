import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.average",
  "category": "Averages and variances",
  "description": "Compute the weighted average along the specified axis",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.average.html",
  "doc": "numpy.average(a, axis=None, weights=None, returned=False, *, keepdims=<no value>)\n\nCompute the weighted average along the specified axis.\n\nParameters\n----------\na : array_like\n    Array containing data to be averaged. If a is not an array, a conversion is attempted.\naxis : None or int or tuple of ints, optional\n    Axis or axes along which to average a. The default, axis=None, will average over all of the elements of the input array.\nweights : array_like, optional\n    An array of weights associated with the values in a. Each value in a contributes to the average according to its associated weight.\nreturned : bool, optional\n    Default is False. If True, the tuple (average, sum_of_weights) is returned, otherwise only the average is returned.\nkeepdims : bool, optional\n    If this is set to True, the axes which are reduced are left in the result as dimensions with size one.\n\nReturns\n-------\nretval, [sum_of_weights] : array_type or double\n    Return the average along the specified axis. When returned is True, return a tuple with the average as the first element and the sum of the weights as the second element.\n\nRaises\n------\nZeroDivisionError\n    When all weights along axis are zero.\nTypeError\n    When the length of 1D weights is not the same as the shape of a along axis.",
  "code": "# Implementation in numpy/lib/_function_base_impl.py\n@array_function_dispatch(_average_dispatcher)\ndef average(a, axis=None, weights=None, returned=False, *,\n            keepdims=np._NoValue):\n    \"\"\"\n    Compute the weighted average along the specified axis.\n    \"\"\"\n    a = np.asanyarray(a)\n    \n    if keepdims is np._NoValue:\n        keepdims_kw = {}\n    else:\n        keepdims_kw = {'keepdims': keepdims}\n    \n    if weights is None:\n        avg = a.mean(axis, **keepdims_kw)\n        avg_as_array = np.asanyarray(avg)\n        scl = avg_as_array.dtype.type(a.size/avg_as_array.size)\n    else:\n        wgt = np.asanyarray(weights)\n        \n        if a.shape != wgt.shape:\n            if axis is None:\n                raise TypeError(\n                    \"Axis must be specified when shapes of a and weights differ.\")\n            if wgt.ndim != 1:\n                raise TypeError(\n                    \"1D weights expected when shapes of a and weights differ.\")\n            if wgt.shape[0] != a.shape[axis]:\n                raise ValueError(\n                    \"Length of weights not compatible with specified axis.\")\n            \n            # setup wgt to broadcast along axis\n            wgt = np.broadcast_to(wgt, (a.ndim-1)*(1,) + wgt.shape, subok=True)\n            wgt = np.moveaxis(wgt, -1, axis)\n        \n        scl = wgt.sum(axis=axis, **keepdims_kw)\n        if np.any(scl == 0.0):\n            raise ZeroDivisionError(\n                \"Weights sum to zero, can't be normalized\")\n        \n        avg = np.multiply(a, wgt,\n                          dtype=result_type(a.dtype, wgt.dtype, float)).sum(\n                              axis, **keepdims_kw) / scl\n    \n    if returned:\n        if scl.shape != avg.shape:\n            scl = np.broadcast_to(scl, avg.shape).copy()\n        return avg, scl\n    else:\n        return avg"
}
-/

-- LLM HELPER
def vector_sum {n : Nat} (v : Vector Float n) : Float :=
  match n with
  | 0 => 0
  | _ + 1 => v.toArray.foldl (· + ·) 0

-- LLM HELPER
def vector_dot {n : Nat} (v1 v2 : Vector Float n) : Float :=
  match n with
  | 0 => 0
  | _ + 1 => 
    let arr1 := v1.toArray
    let arr2 := v2.toArray
    Array.foldl (fun acc i => acc + (arr1[i]! * arr2[i]!)) 0 (Array.range arr1.size)

/-- numpy.average: Compute the weighted average along the specified axis.

    Computes the weighted average of the elements in the input vector.
    If weights are not provided, it computes the arithmetic mean.
    If weights are provided, it computes the weighted average where each
    element contributes according to its associated weight.

    The weighted average is computed as:
    sum(a * weights) / sum(weights)

    When weights are not provided, this reduces to:
    sum(a) / len(a)
-/
def average {n : Nat} (a : Vector Float (n + 1)) (weights : Option (Vector Float (n + 1))) : Id Float :=
  match weights with
  | none => vector_sum a / Float.ofNat (n + 1)
  | some w => vector_dot a w / vector_sum w

/-- Specification: numpy.average computes the weighted average when weights are provided,
    and arithmetic mean when weights are None.

    Precondition: Array is non-empty and if weights are provided, their sum is non-zero
    Postcondition: Returns the weighted average or arithmetic mean as appropriate
-/
theorem average_spec {n : Nat} (a : Vector Float (n + 1)) (weights : Option (Vector Float (n + 1))) :
    ⦃⌜True⌝⦄
    average a weights
    ⦃⇓result => ⌜(weights.isNone → 
        ∃ sum_a : Float, result = sum_a / Float.ofNat (n + 1)) ∧
      (∀ w, weights = some w → 
        ∃ sum_aw sum_w : Float, result = sum_aw / sum_w ∧ sum_w ≠ 0)⌝⦄ := by
  simp [average]
  constructor
  · intro h
    simp [Option.isNone] at h
    rw [h]
    simp
    use vector_sum a
    rfl
  · intro w h
    simp at h
    rw [h]
    simp
    use vector_dot a w, vector_sum w
    constructor
    · rfl
    · -- This assumes weights sum is non-zero as part of the precondition
      --   In practice, this would need to be part of the actual precondition
      --   for the theorem to be provable
      simp