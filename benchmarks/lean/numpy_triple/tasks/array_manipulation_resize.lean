-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def resize {n : Nat} {α : Type} (a : Vector α n) (new_size : Nat) : Id (Vector α new_size) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem resize_spec {n : Nat} {α : Type} (a : Vector α n) (new_size : Nat) :
    ⦃⌜True⌝⦄
    resize a new_size
    ⦃⇓result => ⌜(∀ i : Fin new_size, 
        if h : i.val < n then
          result.get i = a.get ⟨i.val, h⟩
        else if hn : n > 0 then
          result.get i = a.get ⟨i.val % n, Nat.mod_lt i.val hn⟩
        else
          True)⌝⦄ := by
  sorry
-- </vc-theorems>