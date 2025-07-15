import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.isalpha",
  "category": "String information",
  "description": "Returns true for each element if all characters in the string are alphabetic and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isalpha.html",
  "doc": "Returns true for each element if all characters in the string are alphabetic and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isalpha(a):\n    \"\"\"\n    Returns true for each element if all characters in the string are\n    alphabetic and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isalpha\n\n    Examples\n    --------\n    >>> a = np.array(['a', '1', 'a1', ''])\n    >>> np.strings.isalpha(a)\n    array([ True,  False,  False, False])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isalpha_ufunc(a)"
}
-/

/-- numpy.strings.isalpha: Returns true for each element if all characters in the string are alphabetic and there is at least one character, false otherwise.

    Tests whether all characters in each string are alphabetic letters.
    A string is considered alphabetic if:
    1. It contains at least one character
    2. All characters are alphabetic (a-z, A-Z)
    
    Empty strings return false.
    Strings with numbers, symbols, or whitespace return false.
-/
def isalpha {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  a.map (fun s => s ≠ "" ∧ s.toList.all Char.isAlpha)

/-- Specification: numpy.strings.isalpha returns a vector where each element indicates
    whether the corresponding string element contains only alphabetic characters
    and has at least one character.

    Key properties:
    1. Empty strings always return false
    2. Non-empty strings return true iff all characters are alphabetic
    3. Alphabetic characters are those satisfying Char.isAlpha (a-z, A-Z)
    4. Strings with digits, whitespace, or symbols return false
    5. The function is applied element-wise to each string in the vector
    
    Mathematical properties:
    - Monotonicity: removing non-alphabetic characters from a string cannot make isalpha false
    - Compositionality: isalpha(s) = (s.length > 0) ∧ (∀ c ∈ s, Char.isAlpha c)
    - Deterministic: same input always produces same output
-/
theorem isalpha_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isalpha a
    ⦃⇓result => ⌜∀ i : Fin n, 
      -- Core property: result matches the definition
      result.get i = (a.get i ≠ "" ∧ (a.get i).toList.all Char.isAlpha) ∧
      -- Sanity check: empty strings are always false
      (a.get i = "" → result.get i = false) ∧
      -- Sanity check: non-empty strings are true iff all chars are alphabetic
      (a.get i ≠ "" → (result.get i ↔ (a.get i).toList.all Char.isAlpha)) ∧
      -- Mathematical property: if result is true, then string is non-empty
      (result.get i = true → a.get i ≠ "") ∧
      -- Mathematical property: if result is true, then all chars are alphabetic
      (result.get i = true → (a.get i).toList.all Char.isAlpha) ∧
      -- Mathematical property: if string has non-alphabetic char, result is false
      (∃ c ∈ (a.get i).toList, ¬Char.isAlpha c → result.get i = false)⌝⦄ := by
  sorry
