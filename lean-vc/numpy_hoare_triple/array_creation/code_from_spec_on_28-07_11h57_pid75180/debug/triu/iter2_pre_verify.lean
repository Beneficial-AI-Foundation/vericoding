import Std.Do.Triple
import Std.Tactic.Do

Upper triangle of a matrix.
    
Returns a copy of a matrix with the elements below the k-th diagonal zeroed.
- k = 0: main diagonal (default)
- k < 0: include |k| diagonals below the main diagonal
- k > 0: zero out k diagonals above the main diagonal as well
-/

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
    Id (Vector (Vector Float cols) rows) :=
  do
    let processRow (i : Fin rows) : Vector Float cols :=
      Vector.ofFn (fun j : Fin cols => 
        if (i.val : Int) > (j.val : Int) - k then 0 
        else (m.get i).get j)
    
    return Vector.ofFn processRow

theorem correctness {rows cols : Nat} (m : Vector (Vector Float cols) rows) (k : Int) :
    problem_spec triu m k := by
  unfold problem_spec triu
  simp [Std.Do.Triple.Return.return, Id.pure]
  constructor
  · intro i j
    simp [Vector.get_ofFn]
    split_ifs
    · rfl
    · rfl
  constructor
  · intro i j h
    simp [Vector.get_ofFn]
    split_ifs with h'
    · contradiction
    · rfl
  · intro i j h
    simp [Vector.get_ofFn]
    split_ifs with h'
    · rfl
    · contradiction