import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.clip: Clip (limit) the values in an array.

    Given an interval [min, max], values outside the interval are clipped
    to the interval edges. For example, if an interval of [0, 1] is specified,
    values smaller than 0 become 0, and values larger than 1 become 1.

    This is an element-wise operation that bounds each value in the array.
-/
def numpy_clip {n : Nat} (a : Vector Float n) (min max : Float) : Id (Vector Float n) :=
  Vector.ofFn (fun i => 
    let x := a.get i
    if x < min then min else if x > max then max else x)

-- LLM HELPER
lemma Vector.get_ofFn {n : Nat} (f : Fin n → Float) (i : Fin n) : 
  (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get]

/-- Specification: numpy.clip returns a vector with all values clipped to [min, max].

    Precondition: min ≤ max
    Postcondition: Each element in result is clipped to the interval [min, max]
-/
theorem numpy_clip_spec {n : Nat} (a : Vector Float n) (min max : Float) :
    ⦃⌜min ≤ max⌝⦄
    numpy_clip a min max
    ⦃⇓result => ⌜∀ i : Fin n,
      let x := a.get i
      let y := result.get i
      y = if x < min then min else if x > max then max else x⌝⦄ := by
  intro h
  simp [numpy_clip]
  intro i
  rw [Vector.get_ofFn]
  simp