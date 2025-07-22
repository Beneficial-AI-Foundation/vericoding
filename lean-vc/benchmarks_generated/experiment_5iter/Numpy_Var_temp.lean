import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- numpy.var: Variance of array elements.

    Computes the variance of all elements in the array.
    Requires a non-empty array since variance calculation needs the mean.

    The variance measures how spread out the data is from the mean.
    It is calculated as the average of the squared differences from the mean.
-/
def numpy_var (a : Vector Float (n + 1)) : Id Float :=
  let mean := (List.sum (a.toList)) / Float.ofNat (n + 1)
  let variance := (List.sum (a.toList.map (fun x => (x - mean) * (x - mean)))) / Float.ofNat (n + 1)
  pure variance

-- LLM HELPER
lemma pure_spec {α : Type*} (x : α) (P : α → Prop) (h : P x) :
    ⦃⌜True⌝⦄ pure x ⦃⇓ result => ⌜P result⌝⦄ := by
  simp [pure, Id.run]
  exact h

/-- Specification: numpy.var returns the variance of all elements.

    Precondition: True (non-empty constraint is in the type)
    Postcondition: result = mean((x - mean)²)
-/
theorem numpy_var_spec (a : Vector Float (n + 1)) :
    ⦃⌜True⌝⦄
    numpy_var a
    ⦃⇓result =>
      ⌜let mean := (List.sum (a.toList)) / Float.ofNat (n + 1)
      result = (List.sum (a.toList.map (fun x => (x - mean) * (x - mean)))) / Float.ofNat (n + 1)⌝⦄ := by
  unfold numpy_var
  apply pure_spec
  rfl