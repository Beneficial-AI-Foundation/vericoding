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
  rw [sign, Vector.toList_map]
  simp

/-- Specification: Each element is the sign of the corresponding input element -/
theorem sign_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) := by
  intro i
  unfold sign
  constructor
  · intro h
    rw [Vector.getElem_map, sign_element]
    simp [h]
  constructor
  · intro h
    rw [Vector.getElem_map, sign_element]
    have h_not_pos : ¬(a[i] > 0) := by
      intro h_pos
      omega
    simp [h_not_pos, h]
  · intro h
    rw [Vector.getElem_map, sign_element]
    have h_not_pos : ¬(a[i] > 0) := by
      intro h_pos
      omega
    have h_not_zero : ¬(a[i] = 0) := by
      intro h_zero
      omega
    simp [h_not_pos, h_not_zero]

end DafnySpecs.NpSign