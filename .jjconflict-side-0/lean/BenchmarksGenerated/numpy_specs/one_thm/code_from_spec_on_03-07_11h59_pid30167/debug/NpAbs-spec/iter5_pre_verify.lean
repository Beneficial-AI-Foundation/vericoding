namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

/- LLM HELPER -/
lemma Vector.map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (Vector.map f v).toList.length = n := by
  simp [Vector.map, Vector.toList_length]

/- LLM HELPER -/
lemma Vector.map_get {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  simp [Vector.map, Vector.get_mk]

/- LLM HELPER -/
lemma Int.natAbs_nonneg_lemma (x : Int) : Int.natAbs x ≥ 0 := by
  simp [Int.natAbs_nonneg]

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) := by
  constructor
  · rw [abs]
    simp [Vector.map, Vector.toList_length]
  constructor
  · intro i
    rw [abs]
    simp [Vector.map, Vector.get_mk]
  · intro i
    rw [abs]
    simp [Vector.map, Vector.get_mk, Int.natAbs_nonneg]

end NpAbs