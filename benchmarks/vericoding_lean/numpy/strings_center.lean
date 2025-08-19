import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.strings.center",
  "category": "String operations",
  "description": "Return a copy of a with its elements centered in a string of length width",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.center.html",
  "doc": "Return a copy of a with its elements centered in a string of length width.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nwidth : array_like, with any integer dtype\n    The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\nfillchar : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The padding character to use. Default is space.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types\n\nExamples\n--------\n>>> c = np.array(['a1b2','1b2a','b2a1','2a1b']); c\narray(['a1b2', '1b2a', 'b2a1', '2a1b'], dtype='<U4')\n>>> np.strings.center(c, width=9)\narray(['   a1b2  ', '   1b2a  ', '   b2a1  ', '   2a1b  '], dtype='<U9')",
  "code": "def center(a, width, fillchar=' '):\n    \"\"\"\n    Return a copy of \`a\` with its elements centered in a string of\n    length \`width\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    width : array_like, with any integer dtype\n        The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\n    fillchar : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The padding character to use. Default is space.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    ljust, rjust\n\n    Notes\n    -----\n    This function is intended to work with arrays of strings.  The\n    fill character is not applied to numeric types.\n\n    Examples\n    --------\n    >>> c = np.array(['a1b2','1b2a','b2a1','2a1b']); c\n    array(['a1b2', '1b2a', 'b2a1', '2a1b'], dtype='<U4')\n    >>> np.strings.center(c, width=9)\n    array(['   a1b2  ', '   1b2a  ', '   b2a1  ', '   2a1b  '], dtype='<U9')\n    >>> np.strings.center(c, width=9, fillchar='*')\n    array(['***a1b2**', '***1b2a**', '***b2a1**', '***2a1b**'], dtype='<U9')\n    >>> np.strings.center(c, width=1)\n    array(['a1b2', '1b2a', 'b2a1', '2a1b'], dtype='<U4')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    fillchar = np.asanyarray(fillchar, dtype=a.dtype)\n    width = np.asanyarray(width)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(fillchar.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if width.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {width.dtype}\")\n    if np.any(str_len(fillchar) != 1):\n        raise TypeError(\"The fill character must be exactly one character long\")\n    return _center_ljust_rjust_ufunc(a, width, fillchar, 0)"
}
-/

open Std.Do

/-- numpy.strings.center: Return a copy of a with its elements centered in a string of length width.

    Centers strings in a field of given width with optional fill character.
    If the original string length is greater than or equal to the target width,
    the original string is returned unchanged. Otherwise, the string is padded
    symmetrically with the fill character to reach the target width.

    From NumPy documentation:
    - Parameters: a (array_like with StringDType), width (array_like with integer dtype), 
                  fillchar (optional, default ' ') - The padding character
    - Returns: out (ndarray) - Output array with centered strings

    Mathematical Properties:
    1. Length preservation: If original.length >= width, return original unchanged
    2. Symmetric padding: If original.length < width, pad equally on both sides
    3. Padding balance: Left and right padding differ by at most 1 character
    4. Character preservation: Original string appears as substring in result
    5. Width compliance: Result length equals max(original.length, width)
-/
def center {n : Nat} (a : Vector String n) (width : Vector Nat n) (fillchar : Char := ' ') : Id (Vector String n) :=
  return Vector.ofFn (fun i => 
    let str := a.get i
    let w := width.get i
    if str.length ≥ w then 
      str 
    else 
      let padding := w - str.length
      let left_pad := padding / 2
      let right_pad := padding - left_pad
      String.mk (List.replicate left_pad fillchar) ++ str ++ String.mk (List.replicate right_pad fillchar))

/-- Specification: numpy.strings.center returns a vector where each element is the
    corresponding element from the input centered in a field of the specified width.

    Mathematical Properties:
    1. Length preservation: If original string length >= target width, return original
    2. Symmetric padding: If original string length < target width, pad symmetrically
    3. Padding balance: Left and right padding counts differ by at most 1
    4. Character preservation: Original string appears as contiguous substring
    5. Width compliance: Result length equals max(original.length, target_width)
    6. Fill character usage: Padding uses the specified fill character exclusively

    Precondition: True (no special preconditions for string centering)
    Postcondition: For all indices i, result[i] is the centered version of a[i]
-/
theorem center_spec {n : Nat} (a : Vector String n) (width : Vector Nat n) (fillchar : Char := ' ') :
    ⦃⌜True⌝⦄
    center a width fillchar
    ⦃⇓r => ⌜∀ i : Fin n, 
      -- Length preservation: If original string length >= target width, return original
      ((a.get i).length ≥ width.get i → r.get i = a.get i) ∧
      -- Width compliance: Result length equals max(original.length, target_width)
      (r.get i).length = max (a.get i).length (width.get i) ∧
      -- Symmetric padding: If original string length < target width, pad symmetrically
      ((a.get i).length < width.get i → 
        ∃ (left_pad right_pad : Nat), 
          left_pad + (a.get i).length + right_pad = width.get i ∧
          -- Padding should be as equal as possible (differ by at most 1)
          (left_pad = right_pad ∨ left_pad = right_pad + 1) ∧
          -- Left padding is floor(padding/2), right padding is ceiling(padding/2)
          left_pad = (width.get i - (a.get i).length) / 2 ∧
          right_pad = (width.get i - (a.get i).length) - left_pad ∧
          -- Result string structure: left_pad + original + right_pad
          r.get i = (String.mk (List.replicate left_pad fillchar)) ++ (a.get i) ++ (String.mk (List.replicate right_pad fillchar)))⌝⦄ := by
  sorry
