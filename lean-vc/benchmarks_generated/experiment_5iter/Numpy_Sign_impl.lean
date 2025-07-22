import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
instance : DecidableEq Float := Classical.decidableEq

-- LLM HELPER
def sign_element (x : Float) : Float :=
  if x < 0 then -1
  else if x = 0 then 0
  else 1

/-- numpy.sign: Returns an element-wise indication of the sign of a number.

    Returns -1 if x < 0, 0 if x == 0, 1 if x > 0.
    For complex numbers, this is defined as sign(x) = x / |x|.
    For real numbers, this returns the standard signum function.

    Returns an array of the same shape as x, containing the signs.
-/
def numpy_sign {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map sign_element)

-- LLM HELPER
lemma sign_element_spec (x : Float) :
  (x < 0 → sign_element x = -1) ∧
  (x = 0 → sign_element x = 0) ∧
  (x > 0 → sign_element x = 1) := by
  simp [sign_element]
  constructor
  · intro h
    simp [h]
  · constructor
    · intro h
      simp [h]
    · intro h
      simp [h, lt_of_le_of_ne (le_of_not_gt (fun h_neg => lt_irrefl x (lt_trans h_neg h)))]

-- LLM HELPER
lemma vector_get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (v.map f).get i = f (v.get i) := by
  rfl

/-- Specification: numpy.sign returns a vector where each element indicates
    the sign of the corresponding element in x.

    Precondition: True (no special preconditions for sign function)
    Postcondition: For all indices i:
      - result[i] = -1 if x[i] < 0
      - result[i] = 0 if x[i] = 0
      - result[i] = 1 if x[i] > 0
-/
theorem numpy_sign_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_sign x
    ⦃⇓result => ⌜∀ i : Fin n,
      (x.get i < 0 → result.get i = -1) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (x.get i > 0 → result.get i = 1)⌝⦄ := by
  simp [numpy_sign]
  intro i
  rw [vector_get_map]
  exact sign_element_spec (x.get i)