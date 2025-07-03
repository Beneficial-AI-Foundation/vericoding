namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

/- LLM HELPER -/
lemma Vector.map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (Vector.map f v).toList.length = n := by
  simp [Vector.map, Vector.toList_length]

/- LLM HELPER -/
lemma Vector.get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  simp [Vector.map, Vector.get_mk]

/- LLM HELPER -/
lemma Int.natAbs_nonneg (x : Int) : Int.natAbs x ≥ 0 := by
  simp [Int.natAbs]

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) := by
  constructor
  · exact Vector.map_length (fun x => Int.natAbs x) a
  constructor
  · intro i
    exact Vector.get_map (fun x => Int.natAbs x) a i
  · intro i
    rw [Vector.get_map]
    exact Int.natAbs_nonneg (a[i])

end NpAbs