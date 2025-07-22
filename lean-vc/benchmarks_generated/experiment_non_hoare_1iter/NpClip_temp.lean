/-
# NumPy Clip Specification

Port of np_clip.dfy to Lean 4
-/

namespace DafnySpecs.NpClip

/-- Clip values in a vector to a specified range -/
def clip {n : Nat} (a : Vector Float n) (min max : Float) : Vector Float n :=
  Vector.ofFn (fun i => if a[i] < min then min else if a[i] > max then max else a[i])

/-- Specification: The result has the same length as input -/
theorem clip_length {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  ret.toList.length = n := by
  simp [clip]
  rfl

/-- Specification: Values are correctly clipped -/
theorem clip_spec {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  ∀ i : Fin n, if a[i] < min then ret[i] = min
               else if a[i] > max then ret[i] = max
               else ret[i] = a[i] := by
  intro i
  simp [clip]
  rfl

end DafnySpecs.NpClip