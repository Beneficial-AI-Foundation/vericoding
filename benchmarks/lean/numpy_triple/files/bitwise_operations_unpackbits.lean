import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_unpackbits {n : Nat} (a : Vector Nat n) : Id (Vector Nat (n * 8)) :=
  sorry

theorem numpy_unpackbits_spec {n : Nat} (a : Vector Nat n) 
    (h_uint8 : ∀ i : Fin n, a.get i < 256) :
    ⦃⌜∀ i : Fin n, a.get i < 256⌝⦄
    numpy_unpackbits a
    ⦃⇓result => ⌜∀ i : Fin n, ∀ j : Fin 8,
                  result.get ⟨i.val * 8 + j.val, sorry⟩ = 
                  (a.get i / (2 ^ (7 - j.val))) % 2⌝⦄ := by
  sorry
