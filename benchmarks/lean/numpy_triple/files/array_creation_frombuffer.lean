import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def frombuffer {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat) : Id (Vector UInt8 count) :=
  sorry

theorem frombuffer_spec {n : Nat} (buffer : Vector UInt8 n) (count : Nat) (offset : Nat)
    (h_bounds : offset + count ≤ n) (h_offset : offset < n ∨ count = 0) :
    ⦃⌜offset + count ≤ n ∧ (offset < n ∨ count = 0)⌝⦄
    frombuffer buffer count offset
    ⦃⇓result => ⌜∀ i : Fin count, result.get i = buffer.get ⟨offset + i.val, sorry⟩⌝⦄ := by
  sorry
