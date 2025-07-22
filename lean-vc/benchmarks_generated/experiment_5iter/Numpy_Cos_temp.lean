import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.cos: Trigonometric cosine, element-wise.

    The cosine is one of the fundamental functions of trigonometry.
    For a real number x interpreted as an angle in radians, cos(x)
    gives the x-coordinate of the point on the unit circle.

    Returns an array of the same shape as x, containing the cosine of each element.
-/
def numpy_cos {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  Vector.map Float.cos x

-- LLM HELPER
lemma Vector.get_map {α β : Type*} {n : Nat} (f : α → β) (v : Vector α n) (i : Fin n) :
  (Vector.map f v).get i = f (v.get i) := by
  rfl

-- LLM HELPER
lemma Id.pure_spec {α : Type*} (x : α) :
  ⦃⌜True⌝⦄ (pure x : Id α) ⦃⇓result => ⌜result = x⌝⦄ := by
  constructor
  · intro h
    rfl

/-- Specification: numpy.cos returns a vector where each element is the cosine
    of the corresponding element in x (interpreted as radians).

    Precondition: True (no special preconditions for cosine)
    Postcondition: For all indices i, result[i] = Float.cos x[i]
-/
theorem numpy_cos_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    numpy_cos x
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = Float.cos (x.get i)⌝⦄ := by
  unfold numpy_cos
  have h := Id.pure_spec (Vector.map Float.cos x)
  exact h.imp (fun _ => True.intro) (fun h => fun i => by simp [h, Vector.get_map])