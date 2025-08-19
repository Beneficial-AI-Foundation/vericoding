import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def makeRow (n : Nat) (i : Fin n) : Vector Float n :=
  Vector.ofFn fun j => if i = j then (1.0 : Float) else (0.0 : Float)

/-- Return the identity matrix of size n×n.
    The identity matrix is a square matrix with ones on the main diagonal
    and zeros elsewhere. -/
def identity (n : Nat) : Id (Vector (Vector Float n) n) :=
  pure (Vector.ofFn (makeRow n))

-- LLM HELPER
theorem makeRow_spec (n : Nat) (i : Fin n) (j : Fin n) :
    (makeRow n i).get j = if i = j then (1.0 : Float) else (0.0 : Float) := by
  simp [makeRow]
  rw [Vector.get_ofFn]

/-- Specification: identity returns an n×n matrix where:
    - diagonal elements (i,i) are 1.0
    - off-diagonal elements (i,j) where i≠j are 0.0 -/
theorem identity_spec (n : Nat) :
    ⦃⌜True⌝⦄
    identity n
    ⦃⇓result => ⌜∀ i j : Fin n, 
                   (result.get i).get j = if i = j then (1.0 : Float) else (0.0 : Float)⌝⦄ := by
  simp [Triple.entails_def, identity]
  intro i j
  rw [Vector.get_ofFn]
  exact makeRow_spec n i j