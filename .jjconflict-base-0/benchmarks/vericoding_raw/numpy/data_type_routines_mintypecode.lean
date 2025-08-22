import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.mintypecode",
  "category": "Miscellaneous Type Utilities",
  "description": "Return the character for the minimum-size type to which given types can be safely cast",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.mintypecode.html",
  "doc": "Return the character for the minimum-size type to which given types can be safely cast.\n\nParameters\n----------\ntypechars : list of str or array_like\n    If a list of strings, each string should represent a dtype. If array_like, the character representation of the array dtype is used.\ntypeset : str or list of str, optional\n    The set of characters that the returned character is chosen from. The default set is 'GDFgdf'.\ndefault : str, optional\n    The default character if none in typeset matches.\n\nReturns\n-------\ntypechar : str\n    The character representing the minimum-size type found.\n\nExamples\n--------\n>>> np.mintypecode(['d', 'f', 'S'])\n'd'\n>>> x = np.array([1.1, 2-3.j])\n>>> np.mintypecode(x)\n'D'\n>>> np.mintypecode('abceh', default='G')\n'G'",
  "code": "\ndef mintypecode(typechars, typeset='GDFgdf', default='d'):\n    \"\"\"\n    Return the character for the minimum-size type to which given types can\n    be safely cast.\n\n    The returned type character must be the smallest size dtype such that an\n    array of the returned type can handle the data from an array of all types\n    in \`typechars\` (or if \`typechars\` is an array, then its dtype.char).\n\n    Parameters\n    ----------\n    typechars : list of str or array_like\n        If a list of strings, each string should represent a dtype.\n        If array_like, the character representation of the array dtype is used.\n    typeset : str or list of str, optional\n        The set of characters that the returned character is chosen from.\n        The default set is 'GDFgdf'.\n    default : str, optional\n        The default character, this is returned if none of the characters in\n        \`typechars\` matches a character in \`typeset\`.\n\n    Returns\n    -------\n    typechar : str\n        The character representing the minimum-size type found.\n\n    See Also\n    --------\n    dtype, sctype2char, maximum_sctype\n\n    Examples\n    --------\n    >>> import numpy as np\n    >>> np.mintypecode(['d', 'f', 'S'])\n    'd'\n    >>> x = np.array([1.1, 2-3.j])\n    >>> np.mintypecode(x)\n    'D'\n\n    >>> np.mintypecode('abceh', default='G')\n    'G'\n\n    \"\"\"\n    typecodes = ((isinstance(t, str) and t) or asarray(t).dtype.char\n                 for t in typechars)\n    intersection = set(t for t in typecodes if t in typeset)\n    if not intersection:\n        return default\n    if 'F' in intersection and 'd' in intersection:\n        return 'D'\n    return min(intersection, key=lambda x: (typeset.index(x) if x in typeset else len(typeset)))"
}
-/

open Std.Do

/-- NumPy type character to precedence mapping based on the default typeset 'GDFgdf'
    Lower values indicate higher precedence (smaller/more restrictive types) -/
def typechar_precedence : Char → Nat
  | 'g' => 0  -- longdouble (most restrictive in numerical sense)
  | 'd' => 1  -- double
  | 'f' => 2  -- float
  | 'F' => 3  -- csingle (complex float)
  | 'D' => 4  -- cdouble (complex double)
  | 'G' => 5  -- clongdouble (complex long double)
  | _   => 6  -- other types (lowest precedence)

/-- Check if a type character is in the given typeset -/
def char_in_typeset {n : Nat} (c : Char) (typeset : Vector Char n) : Bool :=
  typeset.toList.contains c

/-- Return the character for the minimum-size type to which given types can be safely cast -/
def mintypecode {n m : Nat} (typechars : Vector Char n) (typeset : Vector Char m) (default : Char) : Id Char :=
  sorry

/-- Specification: mintypecode returns the minimum-size type character that can handle all input types -/
theorem mintypecode_spec {n m : Nat} (typechars : Vector Char n) (typeset : Vector Char m) (default : Char) 
    (h_typeset : typeset.toList = ['G', 'D', 'F', 'g', 'd', 'f']) :
    ⦃⌜typeset.toList = ['G', 'D', 'F', 'g', 'd', 'f']⌝⦄
    mintypecode typechars typeset default
    ⦃⇓result => ⌜
      -- Case 1: No input types in typeset - return default
      (∀ c ∈ typechars.toList, ¬(char_in_typeset c typeset) → result = default) ∧
      
      -- Case 2: Special rule - if both 'F' and 'd' are in intersection, return 'D'
      (∃ (intersection : List Char), 
        intersection = (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∧
        intersection.length > 0 ∧
        ('F' ∈ intersection ∧ 'd' ∈ intersection → result = 'D')) ∧
      
      -- Case 3: Normal case - return minimum precedence type from intersection
      (∃ (intersection : List Char),
        intersection = (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∧
        intersection.length > 0 ∧
        ¬('F' ∈ intersection ∧ 'd' ∈ intersection) →
        (result ∈ intersection ∧ 
         ∀ c ∈ intersection, typechar_precedence result ≤ typechar_precedence c)) ∧
      
      -- Validity: result is either from intersection or default
      (result ∈ (typechars.toList.filter (fun c => char_in_typeset c typeset)) ∨ 
       result = default) ∧
      
      -- Safety property: result can handle all input types
      (∀ c ∈ typechars.toList, char_in_typeset c typeset → 
        typechar_precedence result ≤ typechar_precedence c ∨ 
        (result = 'D' ∧ ('F' ∈ typechars.toList ∧ 'd' ∈ typechars.toList)))
    ⌝⦄ := by
  sorry