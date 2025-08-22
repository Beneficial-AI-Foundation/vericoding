namespace NpAbs

def absInt (x : Int) : Int := if x < 0 then -x else x

def abs {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map (fun x => Int.natAbs x) a

-- LLM HELPER
lemma vector_map_get {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v)[i] = f (v[i]) := by
  rfl

-- LLM HELPER
lemma int_natabs_nonneg (x : Int) : Int.natAbs x ≥ 0 := by
  simp [Int.natAbs_nonneg]

theorem abs_spec {n : Nat} (a : Vector Int n) :
  (abs a).toList.length = n ∧
  (∀ i : Fin n, (abs a)[i] = Int.natAbs (a[i])) ∧
  (∀ i : Fin n, (abs a)[i] ≥ 0) :=
by
  constructor
  · simp [abs, Vector.toList_map]
  constructor
  · intro i
    simp [abs, vector_map_get]
  · intro i
    simp [abs, vector_map_get]
    exact int_natabs_nonneg (a[i])

end NpAbs