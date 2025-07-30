import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.islower",
  "category": "String information",
  "description": "Returns true for each element if all cased characters in the string are lowercase and there is at least one cased character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.islower.html",
  "doc": "Returns true for each element if all cased characters in the string are lowercase and there is at least one cased character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def islower(a):\n    \"\"\"\n    Returns true for each element if all cased characters in the\n    string are lowercase and there is at least one cased character,\n    false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.islower\n\n    Examples\n    --------\n    >>> np.strings.islower(\"GHC\")\n    array(False)\n    >>> np.strings.islower(\"ghc\")\n    array(True)\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _islower_ufunc(a)"
}
-/

/-- numpy.strings.islower: Returns true for each element if all cased characters in the string are lowercase and there is at least one cased character, false otherwise.

    Tests whether all cased characters in each string are lowercase.
    A string is considered to satisfy islower if:
    1. It contains at least one cased character (letters that have uppercase/lowercase versions)
    2. All cased characters are lowercase
    3. Non-cased characters (numbers, symbols, whitespace) are ignored for the check
    
    Examples:
    - Empty string "" → false (no cased characters)
    - "123" → false (no cased characters)
    - "abc" → true (all lowercase, has cased characters)
    - "ABC" → false (has uppercase)
    - "aBc" → false (has uppercase)
    - "abc123" → true (has lowercase, no uppercase)
    - "   " → false (no cased characters)
-/
def islower {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  sorry

/-- Specification: numpy.strings.islower returns a vector where each element indicates
    whether the corresponding string element has all cased characters in lowercase
    and contains at least one cased character.

    Mathematical Properties:
    1. A string is considered "islower" if it has at least one cased character AND
       all cased characters are lowercase
    2. Empty strings return false (no cased characters)
    3. Strings with only non-cased characters (digits, symbols, whitespace) return false
    4. Strings with any uppercase letters return false
    5. Strings with at least one lowercase letter and no uppercase letters return true
    
    Edge Cases:
    - Empty string: false (no cased characters)
    - "123": false (no cased characters) 
    - "abc": true (all lowercase, has cased characters)
    - "ABC": false (has uppercase)
    - "aBc": false (has uppercase)
    - "abc123": true (has lowercase, no uppercase)
    - "   ": false (no cased characters)
-/
theorem islower_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    islower a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = 
      ((∃ c ∈ (a.get i).toList, c.isAlpha ∧ c.isLower) ∧ 
       (∀ c ∈ (a.get i).toList, c.isAlpha → c.isLower))⌝⦄ := by
  sorry