import Std.Do.Triple
import Std.Tactic.Do

{
  "name": "numpy.strings.rjust",
  "category": "String operations",
  "description": "Return an array with the elements of a right-justified in a string of length width",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rjust.html",
  "doc": "Return an array with the elements of \`a\` right-justified in a string of length \`width\`.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nwidth : array_like, with any integer dtype\n    The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\nfillchar : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype, optional\n    The character to use for padding. Default is space.\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types",
  "code": "def rjust(a, width, fillchar=' '):\n    \"\"\"\n    Return an array with the elements of \`a\` right-justified in a\n    string of length \`width\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    width : array_like, with any integer dtype\n        The length of the resulting strings, unless \`\`width < str_len(a)\`\`.\n    fillchar : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype, optional\n        The character to use for padding. Default is space.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input types\n\n    See Also\n    --------\n    ljust, center\n\n    Examples\n    --------\n    >>> np.strings.rjust(['hello', 'world'], 10, fillchar='*')\n    array(['*****hello', '*****world'], dtype='<U10')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    fillchar = np.asanyarray(fillchar, dtype=a.dtype)\n    width = np.asanyarray(width)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(fillchar.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if width.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {width.dtype}\")\n    if np.any(str_len(fillchar) != 1):\n        raise TypeError(\"The fill character must be exactly one character long\")\n    return _center_ljust_rjust_ufunc(a, width, fillchar, 2)"
}
-/

open Std.Do

-- LLM HELPER
def String.replicate (s : String) (n : Nat) : String :=
  match n with
  | 0 => ""
  | n + 1 => s ++ String.replicate s n

-- LLM HELPER
def rjust_single (s : String) (width : Nat) (fillchar : String) : String :=
  if s.length >= width then
    s
  else
    let padding_length := width - s.length
    let padding := String.replicate fillchar padding_length
    padding ++ s

/-- numpy.strings.rjust: Return an array with the elements of a right-justified in a string of length width.

    Right-justifies each string in the input array by padding it with the specified
    fill character (default is space) to reach the specified width. If the original
    string is longer than or equal to the width, it remains unchanged.

    Parameters:
    - a: Input array of strings
    - width: Target width for each string
    - fillchar: Character to use for padding (must be exactly one character)
    
    Returns:
    - Array where each string is right-justified to the specified width
    
    Mathematical Properties:
    1. Length preservation: If original.length >= width, return original unchanged
    2. Right-justification: If original.length < width, pad on the left with fillchar
    3. Padding placement: Original string appears as suffix in the result
    4. Character preservation: Original string appears as contiguous substring
    5. Width compliance: Result length equals max(original.length, width)
-/
def rjust {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String) : Id (Vector String n) :=
  pure (a.map (fun s => rjust_single s width fillchar))

-- LLM HELPER
lemma String.replicate_length (s : String) (n : Nat) : 
  (String.replicate s n).length = n * s.length := by
  induction n with
  | zero => simp [String.replicate]
  | succ n ih => 
    simp [String.replicate, String.length_append, ih]
    ring

-- LLM HELPER
lemma rjust_single_length (s : String) (width : Nat) (fillchar : String) :
  (rjust_single s width fillchar).length = max s.length width := by
  simp [rjust_single]
  by_cases h : s.length >= width
  · simp [h]
    exact Nat.max_def.mpr (Or.inl h)
  · simp [h]
    simp [String.length_append, String.replicate_length]
    push_neg at h
    have : s.length < width := h
    simp [Nat.max_def, this]
    omega

-- LLM HELPER
lemma rjust_single_identity (s : String) (width : Nat) (fillchar : String) :
  s.length >= width → rjust_single s width fillchar = s := by
  intro h
  simp [rjust_single, h]

-- LLM HELPER
lemma rjust_single_padding (s : String) (width : Nat) (fillchar : String) :
  s.length < width → 
    (rjust_single s width fillchar).length = width ∧
    (∃ padding : String, rjust_single s width fillchar = padding ++ s ∧ 
        padding.length = width - s.length) ∧
    (rjust_single s width fillchar).endsWith s := by
  intro h
  simp [rjust_single, h]
  constructor
  · simp [String.length_append, String.replicate_length]
    omega
  constructor
  · use String.replicate fillchar (width - s.length)
    constructor
    · rfl
    · simp [String.replicate_length]
  · simp [String.endsWith_append]

/-- Specification: rjust returns a vector where each string is right-justified
    to the specified width using the given fill character.

    Mathematical Properties:
    - Length preservation: Result length is max(original_length, width)
    - Identity: Strings already >= width remain unchanged
    - Right-justification: Original content preserved as suffix, padding on left
    - Minimality: No unnecessary padding beyond required width
    - Fillchar constraint: Padding uses specified fill character
-/
theorem rjust_spec {n : Nat} (a : Vector String n) (width : Nat) (fillchar : String)
    (h_fillchar : fillchar.length = 1) :
    ⦃⌜fillchar.length = 1⌝⦄
    rjust a width fillchar
    ⦃⇓result => ⌜∀ i : Fin n, 
        let orig := a.get i
        let res := result.get i
        -- Core mathematical properties of right-justification
        -- 1. Length invariant: result length is exactly max(orig.length, width)
        res.length = max orig.length width ∧
        -- 2. Identity morphism: strings already >= width are unchanged (f(x) = x when |x| >= w)
        (orig.length ≥ width → res = orig) ∧
        -- 3. Padding morphism: strings < width are extended (f(x) = p ++ x when |x| < w)
        (orig.length < width → 
            res.length = width ∧
            (∃ padding : String, res = padding ++ orig ∧ 
                padding.length = width - orig.length) ∧
            -- Right-justification property: original is preserved as suffix
            res.endsWith orig) ∧
        -- 4. Minimality constraint: no over-padding (efficient operation)
        (orig.length ≥ width → res.length = orig.length) ∧
        -- 5. Exactness constraint: padding achieves exact width requirement
        (orig.length < width → res.length = width) ∧
        -- 6. Consistency constraint: all operations preserve the vector structure
        (orig.length = 0 → res.length = width)⌝⦄ := by
  simp [rjust, Id.pure_bind]
  intro i
  let orig := a.get i
  let res := (a.map (fun s => rjust_single s width fillchar)).get i
  simp [Vector.get_map]
  constructor
  · exact rjust_single_length orig width fillchar
  constructor
  · exact rjust_single_identity orig width fillchar
  constructor
  · exact rjust_single_padding orig width fillchar
  constructor
  · intro h
    rw [rjust_single_identity orig width fillchar h]
  constructor
  · intro h
    have := rjust_single_padding orig width fillchar h
    exact this.1
  · intro h
    rw [rjust_single_length orig width fillchar]
    simp [h, max_def]