import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.sign: Returns an element-wise indication of the sign of a number.

    Returns -1 if x < 0, 0 if x == 0, 1 if x > 0.
    For complex numbers, this is defined as sign(x) = x / |x|.
    For real numbers, this returns the standard signum function.

    Returns an array of the same shape as x, containing the signs.
-/
def numpy_sign {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (x.map (fun val => if val < 0 then -1 else if val = 0 then 0 else 1))

-- LLM HELPER
lemma sign_value_correct (val : Float) :
  let result := if val < 0 then -1 else if val = 0 then 0 else 1
  (val < 0 → result = -1) ∧ (val = 0 → result = 0) ∧ (val > 0 → result = 1) := by
  constructor
  · intro h
    simp [h]
  constructor
  · intro h
    simp [h]
    split
    · contradiction
    · rfl
  · intro h
    simp
    split
    · linarith
    · split
      · linarith
      · rfl

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
  simp [Vector.get_map]
  exact sign_value_correct (x.get i)