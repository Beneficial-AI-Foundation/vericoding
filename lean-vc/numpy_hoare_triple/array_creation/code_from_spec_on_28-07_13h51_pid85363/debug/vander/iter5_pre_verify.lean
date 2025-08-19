import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def makeRow (x : Float) (m : Nat) : Vector Float m :=
  Vector.ofFn (fun j => x ^ ((m - 1 - j.val).toFloat))

def vander {n m : Nat} (x : Vector Float n) : Id (Vector (Vector Float m) n) :=
  return Vector.ofFn (fun i => makeRow (x.get i) m)

-- LLM HELPER
lemma makeRow_get (x : Float) (m : Nat) (j : Fin m) :
  (makeRow x m).get j = x ^ ((m - 1 - j.val).toFloat) := by
  simp [makeRow]
  rw [Vector.get_ofFn]

theorem vander_spec {n m : Nat} (x : Vector Float n) (h_m_pos : m > 0) :
    ⦃⌜m > 0⌝⦄
    vander x
    ⦃⇓result => ⌜∀ (i : Fin n) (j : Fin m), 
                  (result.get i).get j = (x.get i) ^ ((m - 1 - j.val).toFloat)⌝⦄ := by
  simp [vander]
  intro h_m
  intro i j
  rw [Vector.get_ofFn]
  exact makeRow_get (x.get i) m j