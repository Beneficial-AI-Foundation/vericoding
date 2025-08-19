import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.putmask",
  "category": "Boolean/mask indexing",
  "description": "Changes elements of an array based on conditional and input values",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.putmask.html",
  "doc": "Changes elements of an array based on conditional and input values.\n\nSets \`\`a.flat[n] = values[n]\`\` for each n where \`\`mask.flat[n]==True\`\`.\n\nIf \`values\` is not the same size as \`a\` and \`mask\` then it will repeat. This gives behavior different from \`\`a[mask] = values\`\`.\n\nParameters\n----------\na : array_like\n    Target array.\nmask : array_like\n    Boolean mask array. It has to be the same shape as \`a\`.\nvalues : array_like\n    Values to put into \`a\` where \`mask\` is True. If \`values\` is smaller than \`a\` it will be repeated.",
  "code": "# C implementation: from numpy._core import putmask"
}
-/

open Std.Do

/-- Changes elements of an array based on conditional and input values.
    
    This function modifies the target array in-place, setting elements to values
    from the values array where the corresponding mask element is True.
    If values is smaller than the target array, it will repeat cyclically.
    
    Parameters:
    - a: Target array to modify
    - mask: Boolean mask array with same shape as a
    - values: Values to put into a where mask is True
    - m: Size of values array (must be positive for repetition)
-/
def putmask {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) : Id (Vector Float n) :=
  Id.mk (Vector.ofFn (fun i => 
    if mask.get i then 
      values.get ⟨i.val % m, Nat.mod_lt i.val h⟩
    else 
      a.get i))

-- LLM HELPER
lemma vector_ofFn_get {n : Nat} (f : Fin n → Float) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.ofFn, Vector.get]

/-- Specification: putmask changes elements of an array based on conditional and input values.
    
    This comprehensive specification captures:
    1. Elements are changed only where mask is True
    2. Elements are unchanged where mask is False  
    3. Values are taken from the values array with cyclic repetition
    4. The values array must be non-empty (m > 0)
    5. The result has the same size as the input array
    6. The mask and target array must have the same size
-/
theorem putmask_spec {n m : Nat} (a : Vector Float n) (mask : Vector Bool n) (values : Vector Float m) 
    (h : m > 0) :
    ⦃⌜m > 0⌝⦄
    putmask a mask values h
    ⦃⇓result => ⌜(∀ i : Fin n, mask.get i = true → result.get i = values.get ⟨i.val % m, Nat.mod_lt i.val h⟩) ∧
                (∀ i : Fin n, mask.get i = false → result.get i = a.get i) ∧
                (∀ i : Fin n, mask.get i = true → ∃ j : Fin m, result.get i = values.get j)⌝⦄ := by
  simp [Triple.Hoare]
  intro h_pos
  simp [putmask]
  constructor
  · intro i h_mask
    simp [vector_ofFn_get]
    rw [if_pos h_mask]
  constructor
  · intro i h_mask
    simp [vector_ofFn_get]
    rw [if_neg h_mask]
  · intro i h_mask
    use ⟨i.val % m, Nat.mod_lt i.val h⟩
    simp [vector_ofFn_get]
    rw [if_pos h_mask]