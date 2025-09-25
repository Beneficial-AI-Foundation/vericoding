-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromstring {n : Nat} (input : String) (sep : String) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromstring_spec {n : Nat} (input : String) (sep : String) 
    (h_valid : (input.splitOn sep).length = n) 
    (h_nonempty : sep ≠ "") :
    ⦃⌜(input.splitOn sep).length = n ∧ sep ≠ ""⌝⦄
    fromstring (n := n) input sep
    ⦃⇓result => ⌜∀ i : Fin n, 
       (input.splitOn sep)[i.val]!.trim ≠ ""⌝⦄ := by
  sorry
-- </vc-theorems>