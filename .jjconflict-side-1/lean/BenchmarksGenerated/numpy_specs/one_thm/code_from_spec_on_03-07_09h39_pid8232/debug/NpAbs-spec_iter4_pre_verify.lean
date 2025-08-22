namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

/- LLM HELPER -/
lemma Vector.map_length {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) :
  (Vector.map f v).toList.length = n := by
  simp [Vector.map]

/- LLM HELPER -/
lemma Vector.get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  simp [Vector.map]

/- LLM HELPER -/
lemma Int.natAbs_nonneg (x : Int) : Int.natAbs x ≥ 0 := by
  simp [Int.natAbs]

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) := by
  constructor
  · simp [abs, Vector.map]
  constructor
  · intro i
    simp [abs, Vector.map]
  · intro i
    simp [abs, Vector.map, Int.natAbs_nonneg]

end NpAbs