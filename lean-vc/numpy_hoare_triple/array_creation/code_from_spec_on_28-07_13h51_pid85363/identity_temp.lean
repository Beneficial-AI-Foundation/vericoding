import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def makeRow (n : Nat) (rowIdx : Fin n) : Vector Float n :=
  Vector.ofFn fun colIdx => if rowIdx = colIdx then (1.0 : Float) else (0.0 : Float)

/-- Return the identity matrix of size n×n.
    The identity matrix is a square matrix with ones on the main diagonal
    and zeros elsewhere. -/
def identity (n : Nat) : Id (Vector (Vector Float n) n) :=
  pure (Vector.ofFn (makeRow n))

/-- Specification: identity returns an n×n matrix where:
    - diagonal elements (i,i) are 1.0
    - off-diagonal elements (i,j) where i≠j are 0.0 -/
theorem identity_spec (n : Nat) :
    ⦃⌜True⌝⦄
    identity n
    ⦃⇓result => ⌜∀ i j : Fin n, 
                   (result.get i).get j = if i = j then (1.0 : Float) else (0.0 : Float)⌝⦄ := by
  simp [identity]
  intro i j
  simp [Vector.get, Vector.ofFn, makeRow]