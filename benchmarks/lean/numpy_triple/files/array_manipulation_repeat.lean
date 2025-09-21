-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
import Init.Data.Vector.Basic
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def «repeat» {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) : Id (Vector α (n * repeats)) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem repeat_spec {α : Type} {n : Nat} (a : Vector α n) (repeats : Nat) (h_pos : repeats > 0) :
    ⦃⌜repeats > 0⌝⦄
    «repeat» a repeats
    ⦃⇓result => ⌜(∀ i : Fin (n * repeats), 
                   ∃ (k : Fin n), 
                     i.val / repeats = k.val ∧ 
                     result.get i = a.get k) ∧
                  (∀ k : Fin n, ∀ j : Fin repeats,
                   ∃ (idx : Fin (n * repeats)),
                     idx.val = k.val * repeats + j.val ∧
                     result.get idx = a.get k)⌝⦄ := by
  sorry
-- </vc-theorems>