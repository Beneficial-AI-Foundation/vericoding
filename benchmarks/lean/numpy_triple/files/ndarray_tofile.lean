import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def numpy_tofile {n : Nat} (arr : Vector Float n) (filename : String) : Id Unit :=
  sorry

theorem numpy_tofile_spec {n : Nat} (arr : Vector Float n) (filename : String) :
    ⦃⌜True⌝⦄
    numpy_tofile arr filename
    ⦃⇓result => ⌜result = ()⌝⦄ := by
  sorry
