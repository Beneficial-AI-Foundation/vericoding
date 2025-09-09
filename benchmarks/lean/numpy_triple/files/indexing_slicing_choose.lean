import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def choose {n num_choices : Nat} (indices : Vector (Fin num_choices) n) 
          (choices : Vector (Vector Float n) num_choices) : Id (Vector Float n) :=
  sorry

theorem choose_spec {n num_choices : Nat} (indices : Vector (Fin num_choices) n) 
                   (choices : Vector (Vector Float n) num_choices) :
    ⦃⌜True⌝⦄
    choose indices choices
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (choices.get (indices.get i)).get i⌝⦄ := by
  sorry
