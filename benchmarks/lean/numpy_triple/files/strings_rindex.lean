/- 
{
  "name": "numpy.strings.rindex",
  "category": "String information",
  "description": "Like rfind, but raises ValueError when the substring is not found",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rindex.html",
  "doc": "Like \`rfind\`, but raises \`ValueError\` when the substring is not found.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nsub : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nstart, end : array_like, with any integer dtype, optional\n    The range to look in, interpreted as slice notation.\n\nReturns\n-------\nout : ndarray\n    Output array of ints.\n\nRaises\n------\nValueError\n    If substring not found.",
}
-/

/-  For each element, return the highest index in the string where substring is found.
    Unlike rfind, this function requires that the substring be found in each string,
    ensuring all results are non-negative indices. -/

/-  Specification: rindex returns the highest index where substring is found within range.
    The key difference from rfind is that rindex has a stronger precondition:
    the substring must exist in each string within the specified range. -/

import Std.Do.Triple
import Std.Tactic.Do
open Std.Do

-- <vc-helpers>
-- </vc-helpers>

def rindex {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) : Id (Vector Int n) :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

theorem rindex_spec {n : Nat} (a : Vector String n) (sub : Vector String n) (start : Vector Int n) (endPos : Vector Int n) :
    ⦃⌜∀ i : Fin n, 
      -- Valid range bounds
      0 ≤ start.get i ∧ start.get i ≤ endPos.get i ∧
      endPos.get i ≤ (a.get i).length ∧
      -- Substring must exist in each string within the range (precondition for rindex)
      ∃ j : Nat, (start.get i).toNat ≤ j ∧ 
        j + (sub.get i).length ≤ min (endPos.get i + 1).toNat (a.get i).length ∧
        ((a.get i).drop j).take (sub.get i).length = sub.get i⌝⦄
    rindex a sub start endPos
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Result is always non-negative (no -1 values like rfind)
      result.get i ≥ 0 ∧
      -- Result is within the valid search range
      start.get i ≤ result.get i ∧ 
      result.get i ≤ endPos.get i ∧
      -- The substring is found at the returned index
      Int.natAbs (result.get i) + (sub.get i).length ≤ (a.get i).length ∧
      ((a.get i).drop (Int.natAbs (result.get i))).take (sub.get i).length = sub.get i ∧
      -- This is the highest (rightmost) index where substring is found in the range
      (∀ j : Nat, Int.natAbs (result.get i) < j ∧ j + (sub.get i).length ≤ min (endPos.get i + 1).toNat (a.get i).length → 
        ¬(((a.get i).drop j).take (sub.get i).length = sub.get i))⌝⦄ := by
-- <vc-proof>
  sorry
-- </vc-proof>
