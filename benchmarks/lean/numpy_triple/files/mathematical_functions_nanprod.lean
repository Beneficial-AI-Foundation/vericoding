import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def nanprod {n : Nat} (a : Vector Float n) : Id Float :=
  sorry

theorem nanprod_spec {n : Nat} (a : Vector Float n) :
    ⦃⌜True⌝⦄
    nanprod a
    ⦃⇓result => ⌜result = (a.toList.foldl (fun acc x => if x.isNaN then acc else acc * x) 1) ∧
                 ¬result.isNaN ∧
                 (∀ i : Fin n, ¬(a.get i).isNaN → 
                   ∃ filtered : List Float, filtered = (a.toList.filter (fun x => ¬x.isNaN)) ∧
                   result = filtered.foldl (· * ·) 1)⌝⦄ := by
  sorry
