/-
# NumPy Clip Specification

Port of np_clip.dfy to Lean 4
-/

namespace DafnySpecs.NpClip

/-- Clip values in a vector to a specified range -/
def clip {n : Nat} (a : Vector Float n) (min max : Float) : Vector Float n := 
  Vector.mk (a.toList.map (fun x => if x < min then min else if x > max then max else x))

/-- Specification: The result has the same length as input -/
theorem clip_length {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  ret.toList.length = n := by
  simp [clip]
  rw [List.length_map]
  exact a.toList_length

/-- Specification: Values are correctly clipped -/
theorem clip_spec {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  ∀ i : Fin n, if a[i] < min then ret[i] = min
               else if a[i] > max then ret[i] = max
               else ret[i] = a[i] := by
  intro i
  simp [clip]
  rw [Vector.get_mk]
  rw [List.get_map]
  simp

end DafnySpecs.NpClip