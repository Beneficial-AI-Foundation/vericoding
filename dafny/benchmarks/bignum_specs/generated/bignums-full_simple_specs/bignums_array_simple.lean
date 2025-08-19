
-- <vc-dependencies>
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

def valid_bitvec (v : List Int) : Prop :=
  ∀ i, i < v.length → (v[i]? = some 0 ∨ v[i]? = some 1)

def vec2int (v : List Int) : Nat :=
  match v with
  | [] => 0
  | x :: xs => x.toNat + 2 * vec2int xs
-- <\vc-dependencies>
-- <vc-task>
def add (v1 v2 : List Int) : List Int := sorry

theorem add_spec (v1 v2 : List Int)
  (h1 : valid_bitvec v1) (h2 : valid_bitvec v2) :
  valid_bitvec (add v1 v2) ∧ vec2int (add v1 v2) = vec2int v1 + vec2int v2 := by
  sorry
-- <\vc-task>
