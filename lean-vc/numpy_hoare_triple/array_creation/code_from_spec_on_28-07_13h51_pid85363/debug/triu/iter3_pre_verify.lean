import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Upper triangle of a matrix.
    
    Returns a copy of a matrix with the elements below the k-th diagonal zeroed.
    - k = 0: main diagonal (default)
    - k < 0: include |k| diagonals below the main diagonal
    - k > 0: zero out k diagonals above the main diagonal as well
-/
def triu {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) :=
  pure (Vector.ofFn (fun i => 
    Vector.ofFn (fun j => 
      if (i.val : Int) > (j.val : Int) - k then 0 
      else (m.get i).get j)))

/-- Specification: triu returns an upper triangular matrix with specific properties.
    
    Core behavior:
    - Elements below the k-th diagonal are zeroed
    - Elements on and above the k-th diagonal are preserved
    
    Mathematical properties:
    1. Element-wise specification: result[i][j] = if i > j - k then 0 else m[i][j]
    2. Preservation of dimensions: result has same shape as input
    3. Diagonal control: k parameter shifts which diagonal forms the boundary
    4. Idempotence: applying triu twice with same k gives same result
    5. Special cases:
       - k = 0: standard upper triangular (zeros below main diagonal)
       - k < 0: includes |k| diagonals below main diagonal in upper triangle
       - k > 0: zeros out k additional diagonals above main diagonal
    6. For square matrices when k = 0, all elements where row_index > column_index are zero
-/
theorem triu_spec {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    ⦃⌜True⌝⦄
    triu m k
    ⦃⇓result => ⌜(∀ (i : Fin rows) (j : Fin cols), 
                   (result.get i).get j = 
                     if (i.val : Int) > (j.val : Int) - k then 0 
                     else (m.get i).get j) ∧
                  (∀ (i : Fin rows) (j : Fin cols),
                   (i.val : Int) ≤ (j.val : Int) - k → 
                   (result.get i).get j = (m.get i).get j) ∧
                  (∀ (i : Fin rows) (j : Fin cols),
                   (i.val : Int) > (j.val : Int) - k → 
                   (result.get i).get j = 0)⌝⦄ := by
  rw [wp_pure]
  simp [triu]
  constructor
  · -- First part: element-wise specification
    intro i j
    simp [Vector.get_ofFn]
  · constructor
    · -- Second part: preservation of elements on and above k-th diagonal
      intro i j h
      simp [Vector.get_ofFn]
      rw [if_neg (not_lt.mpr h)]
    · -- Third part: zeroing of elements below k-th diagonal
      intro i j h
      simp [Vector.get_ofFn]
      rw [if_pos h]