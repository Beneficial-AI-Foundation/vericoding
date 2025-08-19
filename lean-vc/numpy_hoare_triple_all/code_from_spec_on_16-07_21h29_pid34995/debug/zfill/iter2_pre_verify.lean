import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.zfill",
  "category": "String operations",
  "description": "Return the numeric string left-filled with zeros",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.zfill.html",
  "doc": "Return the numeric string left-filled with zeros.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\nwidth : array_like, with any integer dtype\n    Width of string to left-fill elements in \`a\`\n\nReturns\n-------\nout : ndarray\n    Output array of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input type",
  "code": "def zfill(a, width):\n    \"\"\"\n    Return the numeric string left-filled with zeros\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n    width : array_like, with any integer dtype\n        Width of string to left-fill elements in \`\`a\`\`.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype,\n        depending on input type\n\n    See Also\n    --------\n    str.zfill\n\n    Examples\n    --------\n    >>> np.strings.zfill('1', 3)\n    array('001', dtype='<U3')\n\n    \"\"\"\n    a = np.asanyarray(a)\n    width = np.asanyarray(width)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if width.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {width.dtype}\")\n    return _zfill_ufunc(a, width)"
}
-/

-- LLM HELPER
def repeatChar (c : Char) (n : Nat) : String :=
  String.mk (List.replicate n c)

-- LLM HELPER
def zfillSingle (s : String) (width : Nat) : String :=
  if s.length >= width then
    s
  else if s.length = 0 then
    repeatChar '0' width
  else
    let firstChar := s.get? ⟨0⟩
    if firstChar = some '+' ∨ firstChar = some '-' then
      let sign := s.take 1
      let rest := s.drop 1
      let padding := repeatChar '0' (width - s.length)
      sign ++ padding ++ rest
    else
      let padding := repeatChar '0' (width - s.length)
      padding ++ s

/-- numpy.strings.zfill: Return the numeric string left-filled with zeros.

    Zero-fills each string in the input array by padding it with leading zeros
    to reach the specified width. If the original string is longer than or equal
    to the width, it remains unchanged. This function is specifically designed
    for numeric strings and handles sign prefixes appropriately.

    The function behaves like Python's str.zfill() method:
    - Pads strings with leading zeros to reach the target width
    - Preserves sign characters ('+' or '-') at the beginning
    - Returns original string if it's already >= target width
    
    From NumPy documentation:
    - Parameters: a (array_like) - Input array with string dtype
                  width (int) - Target width for zero-filling
    - Returns: out (ndarray) - Output array with zero-filled strings

    Mathematical Properties:
    1. Length invariant: result length is max(original_length, width)
    2. Identity: strings already >= width remain unchanged
    3. Zero-padding: shorter strings get leading zeros
    4. Sign preservation: leading '+' or '-' characters are preserved
    5. Minimality: no over-padding beyond required width
-/
def zfill {n : Nat} (a : Vector String n) (width : Nat) : Id (Vector String n) :=
  return a.map (fun s => zfillSingle s width)

/-- Specification: numpy.strings.zfill returns a vector where each string element
    is zero-filled to the specified width.

    Mathematical Properties:
    1. Length invariant: Result length is exactly max(original_length, width)
    2. Identity morphism: Strings already >= width are unchanged
    3. Zero-padding morphism: Shorter strings get leading zeros
    4. Sign preservation: Leading '+' or '-' characters are preserved
    5. Minimality: No over-padding beyond required width
    6. Numeric string handling: Appropriate behavior for numeric strings

    The function implements the mathematical transformation:
    f(s, w) = s if |s| >= w
    f(s, w) = zeros(w - |s|) ++ s if |s| < w and s has no sign
    f(s, w) = sign ++ zeros(w - |s|) ++ s[1:] if |s| < w and s starts with sign

    Precondition: width >= 0 (non-negative width requirement)
    Postcondition: Each element is correctly zero-filled to target width
-/
theorem zfill_spec {n : Nat} (a : Vector String n) (width : Nat) :
    ⦃⌜True⌝⦄
    zfill a width
    ⦃⇓r => ⌜∀ i : Fin n, 
      let original := a.get i
      let result := r.get i
      -- Core mathematical properties of zero-filling
      -- 1. Length invariant: result length is exactly max(orig.length, width)
      result.length = max original.length width ∧
      -- 2. Identity morphism: strings already >= width are unchanged
      (original.length ≥ width → result = original) ∧
      -- 3. Zero-padding for short strings without signs
      (original.length < width ∧ 
       original.length > 0 ∧ 
       original.get? ⟨0⟩ ≠ some '+' ∧ 
       original.get? ⟨0⟩ ≠ some '-' → 
         ∃ padding : String, result = padding ++ original ∧ 
           padding.length = width - original.length ∧
           (∀ j : Nat, j < padding.length → padding.get? ⟨j⟩ = some '0')) ∧
      -- 4. Sign preservation: leading '+' or '-' are preserved at start
      (original.length < width ∧ 
       original.length > 0 ∧ 
       (original.get? ⟨0⟩ = some '+' ∨ original.get? ⟨0⟩ = some '-') → 
         ∃ sign : Char, ∃ rest : String, ∃ padding : String,
           original.get? ⟨0⟩ = some sign ∧
           (sign = '+' ∨ sign = '-') ∧
           original = sign.toString ++ rest ∧
           result = sign.toString ++ padding ++ rest ∧
           padding.length = width - original.length ∧
           (∀ j : Nat, j < padding.length → padding.get? ⟨j⟩ = some '0')) ∧
      -- 5. Empty string handling: empty strings become all zeros
      (original.length = 0 → 
         result.length = width ∧ 
         (∀ j : Nat, j < width → result.get? ⟨j⟩ = some '0')) ∧
      -- 6. Minimality constraint: no over-padding
      (original.length ≥ width → result.length = original.length) ∧
      -- 7. Exactness constraint: padding achieves exact width requirement
      (original.length < width → result.length = width) ∧
      -- 8. Correctness constraint: result contains original content
      (original.length < width ∧ original.length > 0 ∧ 
       original.get? ⟨0⟩ ≠ some '+' ∧ original.get? ⟨0⟩ ≠ some '-' → 
         result.drop (width - original.length) = original) ∧
      -- 9. Zero character constraint: padding uses only '0' characters
      (original.length < width → 
         ∀ j : Nat, j < (width - original.length) → result.get? ⟨j⟩ = some '0')⌝⦄ := by
  simp [zfill]
  apply Triple.pure_spec
  intro i
  simp [Vector.get_map]
  let original := a.get i
  let result := zfillSingle original width
  simp [zfillSingle]
  constructor
  · -- Property 1: Length invariant
    by_cases h : original.length >= width
    · simp [h]
      exact Nat.max_left h
    · simp [h]
      by_cases h' : original.length = 0
      · simp [h', repeatChar]
        rw [String.length_mk]
        simp [List.length_replicate]
        rw [Nat.max_def]
        simp [h']
      · simp [h']
        by_cases h'' : original.get? ⟨0⟩ = some '+' ∨ original.get? ⟨0⟩ = some '-'
        · simp [h'']
          rw [String.length_append, String.length_append]
          simp [String.length_take, String.length_drop]
          simp [repeatChar, String.length_mk, List.length_replicate]
          rw [Nat.min_def]
          simp [h']
          rw [Nat.max_def]
          simp [Nat.not_le] at h
          simp [h]
        · simp [h'']
          rw [String.length_append]
          simp [repeatChar, String.length_mk, List.length_replicate]
          rw [Nat.max_def]
          simp [Nat.not_le] at h
          simp [h]
  constructor
  · -- Property 2: Identity morphism
    intro h
    simp [h]
  constructor
  · -- Property 3: Zero-padding for short strings without signs
    intro h_len h_nonempty h_not_plus h_not_minus
    simp [h_len, h_nonempty, h_not_plus, h_not_minus]
    let padding := repeatChar '0' (width - original.length)
    use padding
    constructor
    · rfl
    constructor
    · simp [padding, repeatChar, String.length_mk, List.length_replicate]
    · intro j h_j
      simp [padding, repeatChar, String.get?_mk]
      simp [List.get?_replicate]
      simp [h_j]
  constructor
  · -- Property 4: Sign preservation
    intro h_len h_nonempty h_sign
    simp [h_len, h_nonempty, h_sign]
    cases' h_sign with h_plus h_minus
    · -- Case: starts with '+'
      use '+'
      use original.drop 1
      use repeatChar '0' (width - original.length)
      simp [h_plus, repeatChar]
      constructor
      · rfl
      constructor
      · simp [String.take_drop_cancel]
        apply String.ext
        intro i
        simp [String.get?_append]
        by_cases h_i : i < 1
        · simp [h_i, String.get?_take]
          simp [String.get?_toString]
          simp [h_i]
        · simp [h_i, String.get?_drop]
          simp [Nat.sub_self]
      constructor
      · simp [String.length_mk, List.length_replicate]
      · intro j h_j
        simp [String.get?_mk]
        simp [List.get?_replicate]
        simp [h_j]
    · -- Case: starts with '-'
      use '-'
      use original.drop 1
      use repeatChar '0' (width - original.length)
      simp [h_minus, repeatChar]
      constructor
      · rfl
      constructor
      · simp [String.take_drop_cancel]
        apply String.ext
        intro i
        simp [String.get?_append]
        by_cases h_i : i < 1
        · simp [h_i, String.get?_take]
          simp [String.get?_toString]
          simp [h_i]
        · simp [h_i, String.get?_drop]
          simp [Nat.sub_self]
      constructor
      · simp [String.length_mk, List.length_replicate]
      · intro j h_j
        simp [String.get?_mk]
        simp [List.get?_replicate]
        simp [h_j]
  constructor
  · -- Property 5: Empty string handling
    intro h_empty
    simp [h_empty]
    constructor
    · simp [repeatChar, String.length_mk, List.length_replicate]
    · intro j h_j
      simp [repeatChar, String.get?_mk]
      simp [List.get?_replicate]
      simp [h_j]
  constructor
  · -- Property 6: Minimality constraint
    intro h_ge
    simp [h_ge]
  constructor
  · -- Property 7: Exactness constraint
    intro h_lt
    simp [h_lt]
    by_cases h_empty : original.length = 0
    · simp [h_empty, repeatChar, String.length_mk, List.length_replicate]
    · simp [h_empty]
      by_cases h_sign : original.get? ⟨0⟩ = some '+' ∨ original.get? ⟨0⟩ = some '-'
      · simp [h_sign]
        rw [String.length_append, String.length_append]
        simp [String.length_take, String.length_drop]
        simp [repeatChar, String.length_mk, List.length_replicate]
        rw [Nat.min_def]
        simp [h_empty]
      · simp [h_sign]
        rw [String.length_append]
        simp [repeatChar, String.length_mk, List.length_replicate]
  constructor
  · -- Property 8: Correctness constraint
    intro h_lt h_nonempty h_not_plus h_not_minus
    simp [h_lt, h_nonempty, h_not_plus, h_not_minus]
    simp [String.drop_append]
    simp [repeatChar, String.length_mk, List.length_replicate]
    rw [Nat.sub_self]
    simp
  · -- Property 9: Zero character constraint
    intro h_lt j h_j
    simp [h_lt]
    by_cases h_empty : original.length = 0
    · simp [h_empty, repeatChar, String.get?_mk]
      simp [List.get?_replicate]
      simp [h_j]
    · simp [h_empty]
      by_cases h_sign : original.get? ⟨0⟩ = some '+' ∨ original.get? ⟨0⟩ = some '-'
      · simp [h_sign]
        simp [String.get?_append]
        by_cases h_j_sign : j < 1
        · simp [h_j_sign]
          exfalso
          simp [Nat.lt_one_iff] at h_j_sign
          subst h_j_sign
          simp at h_j
        · simp [h_j_sign]
          simp [String.get?_append]
          by_cases h_j_pad : j - 1 < (width - original.length)
          · simp [h_j_pad]
            simp [repeatChar, String.get?_mk]
            simp [List.get?_replicate]
            simp [h_j_pad]
          · simp [h_j_pad]
      · simp [h_sign]
        simp [String.get?_append]
        by_cases h_j_pad : j < (width - original.length)
        · simp [h_j_pad]
          simp [repeatChar, String.get?_mk]
          simp [List.get?_replicate]
          simp [h_j_pad]
        · simp [h_j_pad]