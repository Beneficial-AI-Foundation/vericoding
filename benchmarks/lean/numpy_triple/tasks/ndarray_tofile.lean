-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numpy_tofile {n : Nat} (arr : Vector Float n) (filename : String) : Id Unit :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numpy_tofile_spec {n : Nat} (arr : Vector Float n) (filename : String) :
    ⦃⌜True⌝⦄
    numpy_tofile arr filename
    ⦃⇓result => ⌜result = ()⌝⦄ := by
  sorry
-- </vc-theorems>