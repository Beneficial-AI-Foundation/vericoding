/-
# NumPy Sign Specification

Port of np_sign.dfy to Lean 4
-/

namespace DafnySpecs.NpSign

-- LLM HELPER
def sign_element (x : Int) : Int :=
  if x > 0 then 1
  else if x = 0 then 0
  else -1

/-- Element-wise sign function for a vector -/
def sign {n : Nat} (a : Vector Int n) : Vector Int n := 
  Vector.map sign_element a

/-- Specification: The result has the same length as input -/
theorem sign_length {n : Nat} (a : Vector Int n) :
  (sign a).toList.length = n := by
  simp [sign, Vector.toList_map]

/-- Specification: Each element is the sign of the corresponding input element -/
theorem sign_spec {n : Nat} (a : Vector Int n) :
  ∀ i : Fin n,
    (a[i] > 0 → (sign a)[i] = 1) ∧
    (a[i] = 0 → (sign a)[i] = 0) ∧
    (a[i] < 0 → (sign a)[i] = -1) := by
  intro i
  constructor
  · intro h
    simp [sign, Vector.get_map, sign_element]
    rw [if_pos h]
  constructor
  · intro h
    simp [sign, Vector.get_map, sign_element]
    rw [if_neg (not_lt.mpr (le_of_eq h)), if_pos h]
  · intro h
    simp [sign, Vector.get_map, sign_element]
    rw [if_neg (not_lt.mpr (le_of_lt h)), if_neg (ne_of_lt h)]

end DafnySpecs.NpSign