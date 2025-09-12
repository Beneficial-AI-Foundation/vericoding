import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.partition",
  "category": "String operations",
  "description": "Partition each element in a around sep",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.partition.html",
  "doc": "Partition each element in \`a\` around \`sep\`.\n\nFor each element in \`a\`, split the element at the first occurrence of \`sep\`, and return a 3-tuple containing the part before the separator, the separator itself, and the part after the separator. If the separator is not found, the first item of the tuple will contain the whole string, and the second and third ones will be empty strings.\n\nParameters\n----------\na : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Input array\nsep : array_like, with \`StringDType\`, \`bytes_\` or \`str_\` dtype\n    Separator to split each string element in \`a\`\n\nReturns\n-------\nout : 3-tuple of ndarrays\n    Three arrays of \`StringDType\`, \`bytes_\` or \`str_\` dtype,\n    depending on input types, with shapes (1,) + a.shape, (...,)",
  "code": "def partition(a, sep):\n    \"\"\"\n    Partition each element in \`\`a\`\` around \`\`sep\`\`.\n\n    Parameters\n    ----------\n    a : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Input array\n    sep : array_like, with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype\n        Separator to split each string element in \`\`a\`\`.\n\n    Returns\n    -------\n    out : 3-tuple:\n        - array with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype with the\n          part before the separator\n        - array with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype with the\n          separator\n        - array with \`\`StringDType\`\`, \`\`bytes_\`\` or \`\`str_\`\` dtype with the\n          part after the separator\n\n    See Also\n    --------\n    str.partition\n\n    Examples\n    --------\n    >>> x = np.array([\"Numpy is nice!\"])\n    >>> np.strings.partition(x, \" \")\n    (array(['Numpy'], dtype='<U5'),\n     array([' '], dtype='<U1'),\n     array(['is nice!'], dtype='<U8'))\n\n    \"\"\"\n    a = np.asanyarray(a)\n    sep = np.asanyarray(sep, dtype=a.dtype)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(sep.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _partition_ufunc(a, sep)"
}
-/

/-- numpy.strings.partition: Partition each element in a around sep.

    Partitions each string in the input vector at the first occurrence of the separator.
    Returns a 3-tuple of vectors: (before_separator, separator, after_separator).
    
    For each element in the input array, splits the element at the first occurrence
    of the separator, and returns three vectors containing the part before the separator,
    the separator itself, and the part after the separator. If the separator is not found,
    the first vector contains the whole string, and the second and third vectors contain
    empty strings.

    From NumPy documentation:
    - Parameters: a (array_like with StringDType), sep (array_like with StringDType)
    - Returns: 3-tuple of ndarrays with StringDType

    Mathematical Properties:
    1. Partition semantics: For each string s, if sep occurs at position i, then:
       - before = s[0:i]
       - separator = sep (if found) or "" (if not found)
       - after = s[i+len(sep):] (if found) or "" (if not found)
    2. Completeness: before ++ separator ++ after = original string (when sep is found)
    3. First occurrence: Only splits at the first occurrence of sep
    4. Not found case: If sep not in string, returns (original_string, "", "")
    5. Preserves vector length: All three result vectors have the same length as input
-/
def partition {n : Nat} (a : Vector String n) (sep : String) : Id (Vector String n × Vector String n × Vector String n) :=
  sorry

/-- Specification: numpy.strings.partition returns a 3-tuple of vectors where each
    element is partitioned around the first occurrence of the separator.

    Mathematical Properties:
    1. Partition correctness: For each index i, the result satisfies partition semantics
    2. Completeness: When separator is found, concatenation reconstructs original string
    3. First occurrence: Only the first occurrence of separator is used for partitioning
    4. Not found case: When separator is not found, returns (original, "", "")
    5. Preserves vector length: All result vectors have the same length as input
    6. Separator consistency: The separator part contains the actual separator or empty string

    Precondition: True (no special preconditions for string partitioning)
    Postcondition: For all indices i, the partition satisfies the partition semantics
-/
theorem partition_spec {n : Nat} (a : Vector String n) (sep : String) :
    ⦃⌜True⌝⦄
    partition a sep
    ⦃⇓result => ⌜let (before, separator, after) := result
                 ∀ i : Fin n, 
                   let original := a.get i
                   let before_i := before.get i
                   let sep_i := separator.get i
                   let after_i := after.get i
                   -- Fundamental partition property: parts reconstruct original string
                   before_i ++ sep_i ++ after_i = original ∧
                   -- Separator correctness: either the separator or empty string
                   (sep_i = sep ∨ sep_i = "") ∧
                   -- Case 1: Separator found - the separator part is exactly the separator
                   (sep_i = sep → sep_i = sep) ∧
                   -- Case 2: Separator not found - before contains whole string, others empty
                   (sep_i = "" → after_i = "" ∧ before_i = original) ∧
                   -- Length preservation: total length is preserved
                   original.length = before_i.length + sep_i.length + after_i.length⌝⦄ := by
  sorry
