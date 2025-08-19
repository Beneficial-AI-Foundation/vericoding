import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def makeRow (x : Float) (m : Nat) : Vector Float m :=
  Vector.ofFn (fun j => x ^ ((m - 1 - j.val).toFloat))

def vander {n m : Nat} (x : Vector Float n) : Id (Vector (Vector Float m) n) :=
  return Vector.ofFn (fun i => makeRow (x.get i) m)

def problem_spec (f : {n m : Nat} → Vector Float n → Id (Vector (Vector Float m) n)) : Prop :=
  ∀ {n m : Nat} (x : Vector Float n) (h_m_pos : m > 0),
    ⦃⌜m > 0⌝⦄
    f x
    ⦃⇓result => ⌜∀ (i : Fin n) (j : Fin m), 
                  (result.get i).get j = (x.get i) ^ ((m - 1 - j.val).toFloat)⌝⦄

-- LLM HELPER
lemma makeRow_get (x : Float) (m : Nat) (j : Fin m) :
  (makeRow x m).get j = x ^ ((m - 1 - j.val).toFloat) := by
  simp [makeRow, Vector.get_ofFn]

-- LLM HELPER  
lemma vector_get_ofFn {α : Type*} {n : Nat} (f : Fin n → α) (i : Fin n) :
  (Vector.ofFn f).get i = f i := by
  simp [Vector.get_ofFn]

theorem correctness {n m : Nat} (x : Vector Float n) (h_m_pos : m > 0) :
    problem_spec (@vander) := by
  intro n m x h_m_pos
  simp [vander]
  intro h_m
  intro i j
  rw [vector_get_ofFn]
  exact makeRow_get (x.get i) m j