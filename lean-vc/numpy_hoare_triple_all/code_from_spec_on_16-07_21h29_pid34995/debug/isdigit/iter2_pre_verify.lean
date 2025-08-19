import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.isdigit",
  "category": "String information",
  "description": "Returns true for each element if all characters in the string are digits, and there is at least one character, false otherwise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.isdigit.html",
  "doc": "Returns true for each element if all characters in the string are digits, and there is at least one character, false otherwise.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n\nReturns\n-------\nout : ndarray\n    Output array of bools",
  "code": "def isdigit(a):\n    \"\"\"\n    Returns true for each element if all characters in the string are\n    digits, and there is at least one character, false otherwise.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of bools\n\n    See Also\n    --------\n    str.isdigit\n\n    Examples\n    --------\n    >>> a = np.array(['a', 'b', '0'], dtype='S1')\n    >>> np.strings.isdigit(a)\n    array([False, False,  True])\n    >>> a = np.array(['a', 'b', '0'], dtype='U1')\n    >>> np.strings.isdigit(a)\n    array([False, False,  True])\n\n    \"\"\"\n    a = np.asanyarray(a)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _isdigit_ufunc(a)"
}
-/

/-- numpy.strings.isdigit: Returns true for each element if all characters in the string are digits, and there is at least one character, false otherwise.

    Tests whether all characters in each string are digits.
    A string is considered to satisfy isdigit if:
    1. It contains at least one character (non-empty)
    2. All characters are digits (0-9)
    
    Empty strings return false.
    Strings with any non-digit characters return false.
    Strings with only digits return true.
    
    This follows the Python str.isdigit() behavior which returns False for empty strings
    and True only if all characters are numeric digits.
-/
def isdigit {n : Nat} (a : Vector String n) : Id (Vector Bool n) :=
  Vector.map (fun s => s ≠ "" ∧ s.all Char.isDigit) a

/-- Specification: numpy.strings.isdigit returns a vector where each element indicates
    whether the corresponding string element contains only digits and is non-empty.

    Precondition: True (no special preconditions)
    Postcondition: For all indices i, result[i] = true if and only if:
    1. The string a[i] is non-empty (not equal to empty string)
    2. All characters in a[i] are digits (satisfy Char.isDigit)
    
    Properties:
    - Empty strings return False
    - Strings with only numeric characters (0-9) return True
    - Strings with any non-numeric characters return False
    - Single digit characters return True
-/
theorem isdigit_spec {n : Nat} (a : Vector String n) :
    ⦃⌜True⌝⦄
    isdigit a
    ⦃⇓result => ⌜∀ i : Fin n, result.get i = (a.get i ≠ "" ∧ (a.get i).all Char.isDigit)⌝⦄ := by
  simp [isdigit]
  simp [Vector.get_map]