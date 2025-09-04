namespace NpClip

def clip {n : Nat} (a : Vector Float n) (min max : Float) : Vector Float n := sorry

theorem clip_spec {n : Nat} (a : Vector Float n) (min max : Float)
  (h : min < max) :
  let ret := clip a min max
  (ret.toList.length = n) ∧
  (∀ i : Fin n, if a[i] < min then ret[i] = min
               else if a[i] > max then ret[i] = max
               else ret[i] = a[i]) := sorry

end NpClip
