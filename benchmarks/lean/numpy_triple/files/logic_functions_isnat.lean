-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

/-- A datetime64 type placeholder representing either a valid datetime or NaT (Not a Time) -/
inductive DateTime64 where
  /-- Valid datetime represented as float (seconds since epoch) -/
  | valid : Float → DateTime64
  /-- NaT (Not a Time) - the datetime equivalent of NaN -/
  | nat : DateTime64
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isnat {n : Nat} (x : Vector DateTime64 n) : Id (Vector Bool n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isnat_spec {n : Nat} (x : Vector DateTime64 n) :
    ⦃⌜True⌝⦄
    isnat x
    ⦃⇓result => ⌜(∀ i : Fin n, result.get i = match x.get i with
                                                | DateTime64.nat => true
                                                | DateTime64.valid _ => false) ∧
                 (∀ i : Fin n, result.get i = true ↔ x.get i = DateTime64.nat) ∧
                 (∀ i : Fin n, result.get i = false ↔ ∃ t : Float, x.get i = DateTime64.valid t)⌝⦄ := by
  sorry
-- </vc-theorems>