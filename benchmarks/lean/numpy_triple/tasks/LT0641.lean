-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def split {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Option Nat) : Id (Vector (List String) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem split_spec {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Option Nat) 
    (h_sep_nonempty : sep ≠ "") :
    ⦃⌜sep ≠ ""⌝⦄
    split a sep maxsplit
    ⦃⇓result => ⌜
      ∀ i : Fin n, 
        let parts := result.get i
        let original := a.get i
        -- Basic correctness: none of the parts equal the separator
        (∀ part ∈ parts, part ≠ sep) ∧
        -- If maxsplit is specified, respect the limit
        (match maxsplit with
         | none => True
         | some limit => parts.length ≤ limit + 1) ∧
        -- The result is non-empty (at least contains the original string if no splits)
        parts.length ≥ 1 ∧
        -- If original is empty, return empty string as single element
        (original.isEmpty → parts = [""]) ∧
        -- If original equals separator, return empty parts
        (original = sep → parts = ["", ""]) ∧
        -- The parts when joined with separator should reconstruct the original (up to maxsplit)
        (match maxsplit with
         | none => String.intercalate sep parts = original
         | some limit => 
           if parts.length ≤ limit + 1 then
             String.intercalate sep parts = original
           else
             -- When maxsplit is reached, last part contains remaining string
             parts.length = limit + 1 ∧ 
             String.intercalate sep (parts.take limit) ++ sep ++ (parts.get ⟨limit, by sorry⟩) = original)⌝⦄ := by
  sorry
-- </vc-theorems>