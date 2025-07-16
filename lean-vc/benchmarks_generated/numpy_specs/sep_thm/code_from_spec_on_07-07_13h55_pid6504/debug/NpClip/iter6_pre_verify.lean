/-
# NumPy Clip Specification

Port of np_clip.dfy to Lean 4
-/

namespace DafnySpecs.NpClip

-- LLM HELPER
def clip_array (arr : Array Float) (min max : Float) : Array Float :=
  arr.map (fun x => if x < min then min else if x > max then max else x)

-- LLM HELPER
theorem clip_array_size (arr : Array Float) (min max : Float) :
  (clip_array arr min max).size = arr.size := by
  simp [clip_array, Array.size_map]

/-- Clip values in a vector to a specified range -/
def clip {n : Nat} (a : Vector Float n) (min max : Float) : Vector Float n := 
  Vector.mk (clip_array a.toArray min max) (by
    rw [clip_array_size]
    exact a.size_toArray)

/-- Specification: The result has the same length as input -/
theorem clip_length {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  ret.toList.length = n := by
  simp [clip, Vector.toList_mk, Array.toList_map]
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
  simp [Vector.get_mk]
  simp [Array.get_map]
  rfl

end DafnySpecs.NpClip