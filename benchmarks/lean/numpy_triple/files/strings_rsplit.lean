-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rsplit {n : Nat} (a : Vector String n) (sep : String) (maxsplit : Nat) : Id (Vector (List String) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>