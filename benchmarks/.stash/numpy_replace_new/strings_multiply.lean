import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.multiply",
  "category": "String operations",
  "description": "Return (a * i), that is string multiple concatenation, element-wise",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.multiply.html",
  "doc": "Return (a * i), that is string multiple concatenation, element-wise.\n\nValues in \`i\` of less than 0 are treated as 0 (which yields an empty string).\n\nParameters\n----------\na : array_like, with \`np.bytes_\` or \`np.str_\` dtype\n    Input array of strings\ni : array_like, with any integer dtype\n    Number of times to repeat each string\n\nReturns\n-------\nout : ndarray\n    Output array of strings\n\nExamples\n--------\n>>> np.strings.multiply('Hello ', 3)\narray('Hello Hello Hello ', dtype='<U18')",
  "code": "def multiply(a, i):\n    \"\"\"\n    Return (a * i), that is string multiple concatenation,\n    element-wise.\n\n    Values in \`\`i\`\` of less than 0 are treated as 0 (which yields an\n    empty string).\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\`, or \`\`str_\`\` dtype\n\n    i : array_like, with any integer dtype\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    Examples\n    --------\n    >>> np.strings.multiply('Hello ', 3)\n    array('Hello Hello Hello ', dtype='<U18')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    i = np.asanyarray(i)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if i.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {i.dtype}\")\n    return _multiply_ufunc(a, i)"
}
-/

/-- Return (a * i), that is string multiple concatenation, element-wise.
    Values in i of less than 0 are treated as 0 (which yields an empty string). -/
def multiply {n : Nat} (a : Vector String n) (i : Vector Int n) : Id (Vector String n) :=
  sorry

/-- Specification: multiply performs element-wise string repetition.
    Each output string is the corresponding input string repeated the specified number of times.
    Negative repetition counts produce empty strings. This comprehensive specification
    captures the core mathematical properties of string multiplication in NumPy. -/
theorem multiply_spec {n : Nat} (a : Vector String n) (i : Vector Int n) :
    ⦃⌜True⌝⦄
    multiply a i
    ⦃⇓result => ⌜-- Core property: Element-wise string repetition
                 (∀ j : Fin n, result.get j = repeat_string (a.get j) (i.get j)) ∧
                 -- Zero/negative repetition property: Always yields empty string
                 (∀ j : Fin n, i.get j ≤ 0 → result.get j = "") ∧
                 -- Identity property: Multiplying by 1 yields the original string
                 (∀ j : Fin n, i.get j = 1 → result.get j = a.get j) ∧
                 -- Zero property: Multiplying by 0 yields empty string
                 (∀ j : Fin n, i.get j = 0 → result.get j = "") ∧
                 -- Empty string property: Empty strings remain empty regardless of repetition
                 (∀ j : Fin n, a.get j = "" → result.get j = "")⌝⦄ := by
  sorry