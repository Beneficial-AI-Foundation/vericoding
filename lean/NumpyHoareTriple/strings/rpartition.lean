import Std.Do.Triple
import Std.Tactic.Do

/-!
{
  "name": "numpy.strings.rpartition",
  "category": "String operations",
  "description": "Partition each element in a around the right-most separator",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.rpartition.html",
  "doc": "Partition (split) each element around the right-most separator.\n\nFor each element in `a`, split the element at the last occurrence of `sep`, and return a 3-tuple containing the part before the separator, the separator itself, and the part after the separator. If the separator is not found, the third item of the tuple will contain the whole string, and the first and second ones will be empty strings.\n\nParameters\n----------\na : array_like, with `StringDType`, `bytes_` or `str_` dtype\n    Input array\nsep : array_like, with `StringDType`, `bytes_` or `str_` dtype\n    Right-most separator to split each string element in `a`\n\nReturns\n-------\nout : 3-tuple of ndarrays\n    Three arrays of `StringDType`, `bytes_` or `str_` dtype,\n    depending on input types",
  "code": "def rpartition(a, sep):\n    \"\"\"\n    Partition (split) each element around the right-most separator.\n\n    For each element in ``a``, split the element at the last occurrence\n    of ``sep``, and return a 3-tuple containing the part before the\n    separator, the separator itself, and the part after the separator.\n    If the separator is not found, the third item of the tuple will\n    contain the whole string, and the first and second ones will be empty\n    strings.\n\n    Parameters\n    ----------\n    a : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n        Input array\n    sep : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n        Separator to split each string element in ``a``.\n\n    Returns\n    -------\n    out : 3-tuple:\n        - array with ``StringDType``, ``bytes_`` or ``str_`` dtype with the\n          part before the separator\n        - array with ``StringDType``, ``bytes_`` or ``str_`` dtype with the\n          separator\n        - array with ``StringDType``, ``bytes_`` or ``str_`` dtype with the\n          part after the separator\n\n    See Also\n    --------\n    str.rpartition\n\n    Examples\n    --------\n    >>> a = np.array(['aAaAaA', '  aA  ', 'abBABba'])\n    >>> np.strings.rpartition(a, 'A')\n    (array(['aAaA', '  a', 'abB'], dtype='<U4'),\n     array(['A', 'A', 'A'], dtype='<U1'),\n     array(['aAaAaA', '  aA  ', 'Bba'], dtype='<U3'))\n\n    \"\"\"\n    a = np.asanyarray(a)\n    sep = np.asanyarray(sep, dtype=a.dtype)\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(sep.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    return _rpartition_ufunc(a, sep)"
}
-/

open Std.Do

/-- numpy.strings.rpartition: Partition each element in a around the right-most separator.

    Partitions each string in the input vector at the last occurrence of the separator.
    Returns a 3-tuple of vectors: (before_separator, separator, after_separator).
    
    For each element in the input array, splits the element at the last occurrence
    of the separator, and returns three vectors containing the part before the separator,
    the separator itself, and the part after the separator. If the separator is not found,
    the third vector contains the whole string, and the first and second vectors contain
    empty strings.

    From NumPy documentation:
    - Parameters: a (array_like with StringDType), sep (array_like with StringDType)
    - Returns: 3-tuple of ndarrays with StringDType

    Mathematical Properties:
    1. Right partition semantics: For each string s, if sep occurs at position i (rightmost), then:
       - before = s[0:i]
       - separator = sep (if found) or "" (if not found)
       - after = s[i+len(sep):] (if found) or "" (if not found)
    2. Completeness: before ++ separator ++ after = original string (when sep is found)
    3. Last occurrence: Only splits at the last occurrence of sep
    4. Not found case: If sep not in string, returns ("", "", original_string)
    5. Preserves vector length: All three result vectors have the same length as input
-/
def rpartition {n : Nat} (a : Vector String n) (sep : String) : Id (Vector String n × Vector String n × Vector String n) :=
  sorry

/-- Specification: numpy.strings.rpartition returns a 3-tuple of vectors where each
    element is partitioned around the last occurrence of the separator.

    Mathematical Properties:
    1. Right partition correctness: For each index i, the result satisfies rpartition semantics
    2. Completeness: When separator is found, concatenation reconstructs original string
    3. Last occurrence: Only the last occurrence of separator is used for partitioning
    4. Not found case: When separator is not found, returns ("", "", original)
    5. Preserves vector length: All result vectors have the same length as input
    6. Separator consistency: The separator part contains the actual separator or empty string

    Precondition: True (no special preconditions for string partitioning)
    Postcondition: For all indices i, the partition satisfies the rpartition semantics
-/
theorem rpartition_spec {n : Nat} (a : Vector String n) (sep : String) :
    ⦃⌜True⌝⦄
    rpartition a sep
    ⦃⇓result => ⌜let (before, separator, after) := result
                 ∀ i : Fin n, 
                   let original := a.get i
                   let before_i := before.get i
                   let sep_i := separator.get i
                   let after_i := after.get i
                   -- Partition property: reconstructs original string
                   before_i ++ sep_i ++ after_i = original ∧
                   -- Separator correctness: either the separator or empty string
                   (sep_i = sep ∨ sep_i = "") ∧
                   -- If separator is found, the separator part matches
                   (sep_i = sep → sep_i = sep) ∧
                   -- If separator is not found, first two parts are empty and after contains whole string
                   (sep_i = "" → before_i = "" ∧ after_i = original)⌝⦄ := by
  sorry