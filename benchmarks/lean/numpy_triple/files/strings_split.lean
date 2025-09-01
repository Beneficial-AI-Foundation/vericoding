/- 
{
  "name": "numpy.strings.split",
  "category": "String operations",
  "description": "For each element in a, return a list of the words in the string, using sep as the delimiter string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.split.html",
  "doc": "For each element in \`a\`, return a list of the words in the string, using \`sep\` as the delimiter string.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    If \`sep\` is not specified or None, any whitespace string is a separator.\nmaxsplit : array_like, with any integer dtype, optional\n    If \`maxsplit\` is given, at most \`maxsplit\` splits are done.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
}
-/

/-  For each element in a vector of strings, return a list of the words in the string, using sep as the delimiter string -/

/-  Specification: split returns a vector where each string is split into a list of substrings 
    based on the separator, with proper handling of maxsplit constraints and reconstruction properties -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def split {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Option Nat) : Id (Vector (List String) n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

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
-- <vc-proof>
  sorry
-- </vc-proof>
