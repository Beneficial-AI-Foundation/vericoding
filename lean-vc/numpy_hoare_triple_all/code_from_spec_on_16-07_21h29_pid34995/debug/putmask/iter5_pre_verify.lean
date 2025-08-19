import Std.Do.Triple
import Std.Tactic.Do

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
  pure (Vector.ofFn (fun i => 
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