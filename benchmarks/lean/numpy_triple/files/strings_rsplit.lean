/- 
{
  "name": "numpy.strings.rsplit",
  "category": "String operations",
  "description": "For each element in a, return a list of the words in the string, using sep as the delimiter string",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rsplit.html",
  "doc": "For each element in \`a\`, return a list of the words in the string, using \`sep\` as the delimiter string.\n\nSplits from the right.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    If \`sep\` is not specified or None, any whitespace string is a separator.\nmaxsplit : array_like, with any integer dtype, optional\n    If \`maxsplit\` is given, at most \`maxsplit\` splits are done.\n\nReturns\n-------\nout : ndarray\n    Output array of objects",
}
-/

/-  For each element in a vector, return a list of the words in the string, using sep as the delimiter string.
    Splits from the right, meaning that splits are made from the right side of the string. -/

/-  Specification: rsplit splits each string in the vector from the right using the given separator.
    The resulting vector contains lists of strings where each list represents the split parts
    of the corresponding input string. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def rsplit {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Nat) : Id (Vector (List String) n) :=
  sorry

theorem rsplit_spec {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Nat) :
    ⦃⌜sep ≠ ""⌝⦄ 
    rsplit a sep maxsplit
    ⦃⇓result => ⌜
      -- Each element in result corresponds to an element in input a
      (∀ i : Fin n, (result.get i).length > 0) ∧
      -- When maxsplit is 0, no splitting occurs
      (maxsplit = 0 → ∀ i : Fin n, result.get i = [a.get i]) ∧
      -- The number of splits is at most maxsplit for each string
      (∀ i : Fin n, (result.get i).length ≤ maxsplit + 1) ∧
      -- When joined back together with separator, we get the original string
      (∀ i : Fin n, maxsplit = 0 → String.intercalate sep (result.get i) = a.get i) ∧
      -- If separator doesn't exist in string, result is single element list
      (∀ i : Fin n, (a.get i).splitOn sep = [a.get i] → result.get i = [a.get i]) ∧
      -- Empty strings split to empty list or single empty string
      (∀ i : Fin n, a.get i = "" → result.get i = [""]) ∧
      -- The split respects the right-to-left order (last occurrences split first)
      (∀ i : Fin n, ∀ parts : List String, result.get i = parts → 
        parts.length > 1 → 
        String.intercalate sep parts = a.get i)⌝⦄ := by
  sorry
