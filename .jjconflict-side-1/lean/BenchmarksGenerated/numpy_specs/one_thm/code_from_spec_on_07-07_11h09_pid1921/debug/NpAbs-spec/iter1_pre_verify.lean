namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) :=
by
  constructor
  · simp [abs, Vector.toList_map]
  constructor
  · intro i
    simp [abs, Vector.get_map]
  · intro i
    simp [abs, Vector.get_map]
    exact Int.natAbs_nonneg (a[i])

end NpAbs