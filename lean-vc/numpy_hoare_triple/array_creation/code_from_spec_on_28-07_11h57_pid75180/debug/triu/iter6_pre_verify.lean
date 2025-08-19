import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

-- LLM HELPER
def problem_spec {rows cols : Nat} (triu_impl : Vector (Vector Float cols) rows → Int → Id (Vector (Vector Float cols) rows)) (m : Vector (Vector Float cols) rows) (k : Int) : Prop :=
  ⦃⌜True⌝⦄
  triu_impl m k
  ⦃⇓result => ⌜(∀ (i : Fin rows) (j : Fin cols), 
                 (result.get i).get j = 
                   if (i.val : Int) > (j.val : Int) - k then 0 
                   else (m.get i).get j) ∧
                (∀ (i : Fin rows) (j : Fin cols),
                 (i.val : Int) ≤ (j.val : Int) - k → 
                 (result.get i).get j = (m.get i).get j) ∧
                (∀ (i : Fin rows) (j : Fin cols),
                 (i.val : Int) > (j.val : Int) - k → 
                 (result.get i).get j = 0)⌝⦄

def triu {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int := 0) : 
    Id (Vector (Vector Float cols) rows) := pure (
  Vector.ofFn (fun i : Fin rows => 
    Vector.ofFn (fun j : Fin cols => 
      if (i.val : Int) > (j.val : Int) - k then 0 
      else (m.get i).get j)))

theorem correctness {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    problem_spec triu m k := by
  unfold problem_spec triu
  rw [Std.Do.Triple]
  constructor
  · simp
  · simp [pure]
    constructor
    · intro i j
      simp [Vector.get_ofFn]
      by_cases h : (i.val : Int) > (j.val : Int) - k <;> simp [h]
    constructor
    · intro i j h
      simp [Vector.get_ofFn]
      simp [if_neg]
      intro h'
      linarith
    · intro i j h
      simp [Vector.get_ofFn]
      simp [if_pos h]