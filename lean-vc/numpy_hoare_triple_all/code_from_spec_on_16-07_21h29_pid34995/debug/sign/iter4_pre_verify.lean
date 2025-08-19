import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.sign",
  "description": "Returns an element-wise indication of the sign of a number",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.sign.html",
  "doc": "Returns an element-wise indication of the sign of a number.\n\nThe sign function returns -1 if x < 0, 0 if x==0, 1 if x > 0. nan is returned for nan inputs.",
  "code": "# Universal function (ufunc) implemented in C\n# Returns element-wise indication of sign\ndef sign(x, /, out=None, *, where=True, casting='same_kind', order='K', dtype=None, subok=True):\n    '''Returns element-wise indication of the sign of a number'''\n    # Handle array conversion\n    x = np.asanyarray(x)\n    \n    # Returns: -1 if x < 0, 0 if x == 0, 1 if x > 0\n    # For complex numbers: sign(x) = x / |x| (except 0 -> 0)\n    # NaN inputs return NaN\n    return _apply_ufunc(_sign_impl, x, out=out, where=where,\n                       casting=casting, order=order, dtype=dtype, subok=subok)"
}
-/

-- LLM HELPER
instance : DecidableEq Float := Classical.decidableEq

-- LLM HELPER
def sign_elem (x : Float) : Float :=
  if x < 0 then -1
  else if x = 0 then 0
  else 1

/-- Returns an element-wise indication of the sign of a number -/
def sign {n : Nat} (x : Vector Float n) : Id (Vector Float n) :=
  pure (Vector.map sign_elem x)

-- LLM HELPER
lemma sign_elem_spec (x : Float) :
  (x < 0 → sign_elem x = -1) ∧
  (x = 0 → sign_elem x = 0) ∧
  (x > 0 → sign_elem x = 1) := by
  simp [sign_elem]
  constructor
  · intro h
    simp [h]
    have : ¬(x = 0) := by linarith
    simp [this]
  · constructor
    · intro h
      simp [h]
    · intro h
      have : ¬(x < 0) := by linarith
      have : ¬(x = 0) := by linarith
      simp [this]

-- LLM HELPER
lemma triple_id_intro {P : Prop} {Q : α → Prop} (f : Id α) (h : P → Q (f.run)) :
    ⦃⌜P⌝⦄ f ⦃⇓result => ⌜Q result⌝⦄ := by
  intro _ hp
  simp [Id.run]
  exact h hp

/-- Specification: sign returns -1 for negative numbers, 0 for zero, 1 for positive numbers -/
theorem sign_spec {n : Nat} (x : Vector Float n) :
    ⦃⌜True⌝⦄
    sign x
    ⦃⇓result => ⌜∀ i : Fin n, 
      (x.get i < 0 → result.get i = -1) ∧
      (x.get i = 0 → result.get i = 0) ∧
      (x.get i > 0 → result.get i = 1)⌝⦄ := by
  apply triple_id_intro
  intro _
  intro i
  simp [sign, Vector.get_map]
  exact sign_elem_spec (x.get i)