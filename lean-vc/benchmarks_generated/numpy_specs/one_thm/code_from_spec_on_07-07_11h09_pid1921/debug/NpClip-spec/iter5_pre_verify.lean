namespace NpClip

def clip {n : Nat} (a : Vector Float n) (min max : Float) : Vector Float n := 
  Vector.mk (a.toList.map (fun x => if x < min then min else if x > max then max else x)).toArray
   (by simp [List.length_map, Vector.toList_length])

-- LLM HELPER
lemma clip_length {n : Nat} (a : Vector Float n) (min max : Float) :
  (clip a min max).toList.length = n := by
  simp [clip, List.length_map, Vector.toList_length]

-- LLM HELPER
lemma clip_get {n : Nat} (a : Vector Float n) (min max : Float) (i : Fin n) :
  (clip a min max)[i] = if a[i] < min then min else if a[i] > max then max else a[i] := by
  simp [clip, Vector.get_mk, List.get_map]

theorem clip_spec {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  (ret.toList.length = n) ∧
  (∀ i : Fin n, if a[i] < min then ret[i] = min
               else if a[i] > max then ret[i] = max
               else ret[i] = a[i]) := by
  constructor
  · exact clip_length a min max
  · intro i
    exact clip_get a min max i

end NpClip