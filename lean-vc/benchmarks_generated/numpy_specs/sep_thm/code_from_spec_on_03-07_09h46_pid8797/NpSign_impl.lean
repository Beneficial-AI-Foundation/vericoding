/-
# NumPy Sign Specification

Port of np_sign.dfy to Lean 4
-/

namespace DafnySpecs.NpSign

/- LLM HELPER -/
def sign_element (x : Int) : Int :=
  if x > 0 then 1
  else if x = 0 then 0
  else -1

/-- Element-wise sign function for a vector -/
def sign {n : Nat} (a : Vector Int n) : Vector Int n := 
  a.map sign_element

/-- Specification: The result has the same length as input -/
theorem sign_length {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n := by
  simp [sign]
  rw [Vector.toList_map]
  simp [Vector.toList_length]

/- LLM HELPER -/
lemma sign_element_spec (x : Int) :
  (0 < x → sign_element x = 1) ∧ (x = 0 → sign_element x = 0) ∧ (x < 0 → sign_element x = -1) := by
  constructor
  · intro h
    simp [sign_element, h]
  constructor
  · intro h
    simp [sign_element, h]
  · intro h
    simp [sign_element]
    split
    · rename_i h_pos
      exfalso
      exact not_lt.mpr (le_of_lt h_pos) h
    · split
      · rename_i h_eq
        exfalso
        rw [h_eq] at h
        exact lt_irrefl 0 h
      · rfl

/-- Specification: Each element is the sign of the corresponding input element -/
theorem sign_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) := by
  intro i
  simp [sign]
  rw [Vector.get_map]
  exact sign_element_spec (a[i])

end DafnySpecs.NpSign