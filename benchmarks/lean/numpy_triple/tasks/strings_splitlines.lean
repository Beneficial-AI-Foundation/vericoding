-- <vc-preamble>
import Std.Do.Triple
import Std.Tactic.Do
open Std.Do
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def splitlines {n : Nat} (a : Vector String n) (keepends : Bool) : Id (Vector (List String) n) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem splitlines_spec {n : Nat} (a : Vector String n) (keepends : Bool) :
    ⦃⌜True⌝⦄
    splitlines a keepends
    ⦃⇓result => ⌜
      ∀ i : Fin n, 
        let lines := result.get i
        let original := a.get i
        -- The result is always non-empty (at least contains one element)
        lines.length ≥ 1 ∧
        -- If original is empty, return empty string as single element
        (original.isEmpty → lines = [""]) ∧
        -- If original has no line breaks, return original as single element
        (¬original.contains '\n' ∧ ¬original.contains '\r' → lines = [original]) ∧
        -- If keepends is false, no line in result contains line break characters
        (¬keepends → ∀ line ∈ lines, ¬line.contains '\n' ∧ ¬line.contains '\r') ∧
        -- If keepends is false, no line endings in result
        (¬keepends → ∀ line ∈ lines, ¬line.endsWith "\n" ∧ ¬line.endsWith "\r" ∧ ¬line.endsWith "\r\n") ∧
        -- If keepends is true, only the last line may lack line ending
        (keepends → ∀ j : Fin lines.length, j.val < lines.length - 1 → 
          let line := lines.get j
          line.endsWith "\n" ∨ line.endsWith "\r" ∨ line.endsWith "\r\n") ∧
        -- Basic reconstruction property: joining with newlines gives back normalized original
        (¬keepends → String.intercalate "\n" lines = (original.replace "\r\n" "\n").replace "\r" "\n") ∧
        -- Line count property: lines should be related to line break count
        (¬original.contains '\n' ∧ ¬original.contains '\r' → lines.length = 1) ∧
        -- Empty string property
        (original = "" → lines = [""]) ∧
        -- Single newline property
        (original = "\n" → (if keepends then lines = ["\n"] else lines = ["", ""]))⌝⦄ := by
  sorry
-- </vc-theorems>