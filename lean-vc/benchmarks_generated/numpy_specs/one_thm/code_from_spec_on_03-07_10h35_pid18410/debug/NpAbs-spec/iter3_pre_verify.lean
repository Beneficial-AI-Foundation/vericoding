namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

/- LLM HELPER -/
lemma Vector.map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (Vector.map f v).toList.length = n := by
  rw [Vector.map_toList]
  rw [List.length_map]
  exact v.toList_length

/- LLM HELPER -/
lemma Vector.map_get {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  rw [Vector.get_map]

/- LLM HELPER -/
lemma Int.natAbs_nonneg (x : Int) : Int.natAbs x ≥ 0 := by
  exact Int.natAbs_nonneg

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) := by
  constructor
  · simp [abs]
    rw [Vector.toList_map]
    rw [List.length_map]
    exact a.toList_length
  constructor
  · intro i
    simp [abs]
    rw [Vector.get_map]
  · intro i
    simp [abs]
    rw [Vector.get_map]
    exact Int.natAbs_nonneg (a[i])

end NpAbs