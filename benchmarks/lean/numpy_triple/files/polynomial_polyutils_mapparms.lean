-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mapparms (old new : Vector Float 2) : Id (Float × Float) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mapparms_spec (old new : Vector Float 2) 
    (h_old_distinct : old.get ⟨0, by simp⟩ ≠ old.get ⟨1, by simp⟩) :
    ⦃⌜old.get ⟨0, by simp⟩ ≠ old.get ⟨1, by simp⟩⌝⦄
    mapparms old new
    ⦃⇓result => ⌜let (offset, scale) := result
                  let oldlen := old.get ⟨1, by simp⟩ - old.get ⟨0, by simp⟩
                  let newlen := new.get ⟨1, by simp⟩ - new.get ⟨0, by simp⟩
                  -- The linear map L(x) = offset + scale*x maps old domain to new domain
                  offset + scale * old.get ⟨0, by simp⟩ = new.get ⟨0, by simp⟩ ∧
                  offset + scale * old.get ⟨1, by simp⟩ = new.get ⟨1, by simp⟩ ∧
                  -- Mathematical relationships from numpy implementation
                  scale = newlen / oldlen ∧
                  offset = (old.get ⟨1, by simp⟩ * new.get ⟨0, by simp⟩ - old.get ⟨0, by simp⟩ * new.get ⟨1, by simp⟩) / oldlen⌝⦄ := by
  sorry
-- </vc-theorems>