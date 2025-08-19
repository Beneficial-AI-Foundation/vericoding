import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.strings.isupper",
  "category": "String information",
  "description": "Return true for each element if all cased characters in the string are uppercase and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isupper.html",
  "doc": "Return true for each element if all cased characters in the string are uppercase and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isupper(a):\n    \"\"\"\n    Return true for each element if all cased characters in the\n    string are uppercase and there is at least one character, false\n    otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isupper\n\n    Examples\n    --------\n    >>> np.strings.isupper(\"GHC\")\n    array(True)\n    >>> a = np.array([\"hello\", \"HELLO\", \"Hello\"])\n    >>> np.strings.isupper(a)\n    array([False,  True, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isupper_ufunc(a)"
}
-/

open Std.Do

-- LLM HELPER
def stringIsUpper (s : String) : Bool :=
  let chars := s.toList
  chars.length > 0 ∧ 
  (∃ c ∈ chars, c.isAlpha) ∧
  (∀ c ∈ chars, c.isAlpha → c.isUpper)

/-- Checks if all cased characters in each string are uppercase and there is at least one character -/
def isupper {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  return ⟨Array.map stringIsUpper a.toArray, by simp [Array.size_map]⟩

/-- Specification: isupper returns true for each element if all cased characters 
    in the string are uppercase and there is at least one character, false otherwise.
    Mathematical properties:
    1. Empty strings return false
    2. Strings with no cased characters return false  
    3. Strings with mixed case return false
    4. Strings with all cased characters uppercase return true -/
theorem isupper_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isupper a
    ⦃⇓result => ⌜∀ i : Fin n, 
                   let s := a.get i
                   let chars := s.toList
                   result.get i = (chars.length > 0 ∧ 
                                  (∃ c ∈ chars, c.isAlpha) ∧
                                  (∀ c ∈ chars, c.isAlpha → c.isUpper))⌝⦄ := by
  unfold isupper
  simp [Triple.pure]
  intro i
  simp [Vector.get, stringIsUpper]
  rfl