namespace NpSign

/- LLM HELPER -/
def signInt (x : Int) : Int :=
  if x > 0 then 1
  else if x = 0 then 0
  else -1

def sign {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map signInt a

/- LLM HELPER -/
lemma signInt_spec (x : Int) :
  (x > 0 → signInt x = 1) ∧
  (x = 0 → signInt x = 0) ∧
  (x < 0 → signInt x = -1) := by
  constructor
  · intro h
    simp [signInt]
    exact if_pos h
  constructor
  · intro h
    simp [signInt]
    rw [if_neg (not_lt.mpr (le_of_eq h.symm))]
    exact if_pos h
  · intro h
    simp [signInt]
    rw [if_neg (not_lt.mpr (le_of_lt h))]
    rw [if_neg (ne_of_lt h)]

theorem sign_spec {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n ∧
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) := by
  constructor
  · simp [sign]
    rw [Vector.toList_map]
    exact List.length_map _ _
  · intro i
    simp [sign]
    rw [Vector.get_map]
    exact signInt_spec (a[i])

end NpSign