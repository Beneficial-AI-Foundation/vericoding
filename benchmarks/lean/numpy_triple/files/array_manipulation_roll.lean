-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def roll {n : Nat} {α : Type} (a : Vector α n) (shift : Int) : Id (Vector α n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem roll_spec {n : Nat} {α : Type} (a : Vector α n) (shift : Int) :
    ⦃⌜True⌝⦄
    roll a shift
    ⦃⇓result => ⌜(n = 0 → result = a) ∧ 
                 (n > 0 → ∀ i : Fin n, 
                   let srcIdx := ((i.val : Int) - shift) % (n : Int)
                   let normalizedIdx := if srcIdx < 0 then srcIdx + n else srcIdx
                   result.get i = a.get ⟨normalizedIdx.toNat, by sorry⟩)⌝⦄ := by
  sorry
-- </vc-theorems>