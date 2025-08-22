namespace NpInvert

def invert {n : Nat} (bitWidth : Nat) (a : Vector Nat n) : Vector Nat n := 
  a.map (fun x => (2^bitWidth - 1) - x)

theorem invert_spec {n : Nat} (bitWidth : Nat) (a : Vector Nat n) :
  (invert bitWidth a).toList.length = n ∧
  ∀ i : Fin n, (invert bitWidth a)[i] = (2^bitWidth - 1) - a[i] := by
  constructor
  · simp [invert, Vector.toList_map]
  · intro i
    simp [invert, Vector.get_map_val]

end NpInvert