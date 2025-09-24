-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- Abstract file representation for specification purposes
structure FileData where
  content : List Float
  valid : Bool
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fromfile (n : Nat) (file : FileData) (count : Int) (offset : Nat) : Id (Vector Float n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem fromfile_spec (n : Nat) (file : FileData) (count : Int) (offset : Nat)
    (h_valid : file.valid = true)
    (h_count : count = n ∨ count = -1)
    (h_offset : offset ≤ file.content.length)
    (h_sufficient : file.content.length - offset ≥ n) :
    ⦃⌜file.valid = true ∧
      (count = n ∨ count = -1) ∧
      offset ≤ file.content.length ∧
      file.content.length - offset ≥ n⌝⦄
    fromfile n file count offset
    ⦃⇓result => ⌜∀ i : Fin n,
      result.get i = file.content.get! (offset + i.val) ∧
      n ≤ file.content.length - offset⌝⦄ := by
  sorry
-- </vc-theorems>