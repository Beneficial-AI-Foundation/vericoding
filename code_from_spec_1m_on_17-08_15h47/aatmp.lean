import Std
open Std.Do




def maax (a : Int) (b : Int) : Id Int :=
  sorry

theorem max_spec (a : Int) (b : Int)  :
    ⦃⌜True⌝⦄
    maax a b
    ⦃⇓result => ⌜result ≥ a ∧ result ≥ b ∧ (result == a ∨ result == b)⌝⦄ := by
  sorry  -- TODO: implement proof
