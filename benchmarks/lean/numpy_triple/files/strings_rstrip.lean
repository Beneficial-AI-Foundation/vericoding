-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rstrip {n : Nat} (a : Vector String n) (chars : Option String) : Id (Vector String n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rstrip_spec {n : Nat} (a : Vector String n) (chars : Option String) :
    ⦃⌜True⌝⦄
    rstrip a chars
    ⦃⇓result => ⌜∀ i : Fin n, 
      let original := a.get i
      let stripped := result.get i
      -- Case 1: When chars is None, use trimRight (removes whitespace)
      (chars.isNone → stripped = original.trimRight) ∧
      -- Case 2: When chars is provided, remove characters from that set
      (chars.isSome → 
        ∃ suffix : String, 
          -- The result is the original string with the suffix removed
          (original = stripped ++ suffix) ∧
          -- The suffix consists only of characters from the chars set
          (∀ c : Char, c ∈ suffix.toList → c ∈ chars.get!.toList) ∧
          -- Maximal stripping: result doesn't end with any character from chars set
          (stripped = "" ∨ 
           ∀ c : Char, c ∈ chars.get!.toList → 
             stripped.back ≠ c) ∧
          -- Length constraint: result is never longer than original
          (stripped.length ≤ original.length))⌝⦄ := by
  sorry
-- </vc-theorems>