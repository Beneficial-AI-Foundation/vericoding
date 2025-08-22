import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
{
  "name": "numpy.strings.replace",
  "category": "String operations",
  "description": "For each element in a, return a copy of the string with occurrences of substring old replaced by new",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.replace.html",
  "doc": "For each element in `a`, return a copy of the string with occurrences of substring `old` replaced by `new`.\n\nParameters\n----------\na : array_like, with `StringDType`, `bytes_` or `str_` dtype\nold : array_like, with `StringDType`, `bytes_` or `str_` dtype\nnew : array_like, with `StringDType`, `bytes_` or `str_` dtype\ncount : array_like, with any integer dtype, optional\n    Maximum number of occurrences to replace. -1 (the default) means replace all occurrences.\n\nReturns\n-------\nout : ndarray\n    Output array of `StringDType`, `bytes_` or `str_` dtype,\n    depending on input types",
  "code": "def replace(a, old, new, count=-1):\n    \"\"\"\n    For each element in ``a``, return a copy of the string with\n    occurrences of substring ``old`` replaced by ``new``.\n\n    Parameters\n    ----------\n    a : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n\n    old, new : array_like, with ``StringDType``, ``bytes_`` or ``str_`` dtype\n\n    count : array_like, with any integer dtype\n        If the optional argument ``count`` is given, only the first\n        ``count`` occurrences are replaced.\n\n    Returns\n    -------\n    out : ndarray\n        Output array of ``StringDType``, ``bytes_`` or ``str_`` dtype,\n        depending on input types\n\n    See Also\n    --------\n    str.replace\n\n    Examples\n    --------\n    >>> a = np.array([\"That is a mango\", \"Monkeys eat mangos\"])\n    >>> np.strings.replace(a, 'mango', 'banana')\n    array(['That is a banana', 'Monkeys eat bananas'], dtype='<U19')\n\n    >>> a = np.array([\"The dish is fresh\", \"This is it\"])\n    >>> np.strings.replace(a, 'is', 'was')\n    array(['The dwash was fresh', 'Thwas was it'], dtype='<U19')\n\n    \"\"\"\n    from ..strings import count as count_sub\n    \n    a = np.asanyarray(a)\n    old = np.asanyarray(old, dtype=a.dtype)\n    new = np.asanyarray(new, dtype=a.dtype)\n    count = np.asanyarray(count)\n\n    if not _is_string_dtype(a.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(old.dtype):\n        raise TypeError(\"string operation on non-string array\")\n    if not _is_string_dtype(new.dtype):\n        raise TypeError(\"string operation on non-string array\")\n\n    if count.dtype.kind not in \"iu\":\n        raise TypeError(f\"expected an integer array-like, got {count.dtype}\")\n\n    max_int64 = np.array(np.iinfo(np.int64).max)\n    count = np.where(count < 0, max_int64, count)\n\n    # Make sure we find the longest string length by looking at the result\n    # with count == -1\n    counts = count_sub(a, old)\n    string_length = str_len(a) - str_len(old) * counts + str_len(new) * counts\n\n    # if count != -1, we replace at most count occurrences, so the new\n    # string length is guaranteed to be at least\n    # str_len(a) - str_len(old) * count + str_len(new) * count\n    count = counts if np.all(count == -1) else np.minimum(counts, count)\n    string_length = np.where(count == -1, string_length,\n                           str_len(a) - str_len(old) * count + str_len(new) * count)\n    max_string_length = np.max(string_length)\n    if hasattr(a.dtype, \"na_object\") and a.dtype.na_object is None:\n        # StringDType\n        out_dtype = type(a.dtype)()\n    else:\n        # fixed-length string dtype\n        out_dtype = f\"{a.dtype.char}{max_string_length}\"\n    return _replace_ufunc(a, old, new, count, _dtype=out_dtype)"
}
-/

/-- numpy.strings.replace: For each element in a, return a copy of the string with 
    occurrences of substring old replaced by new.

    Replaces occurrences of the substring 'old' with 'new' in each string element.
    The replacement is done from left to right, and if count is specified, only
    the first 'count' occurrences are replaced. If count is -1 or negative,
    all occurrences are replaced.
-/
def replace {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) : Id (Vector String n) :=
  sorry

/-- Specification for numpy.strings.replace: Returns a vector where each element is the
    result of replacing occurrences of old substring with new substring.

    Mathematical Properties:
    1. Element-wise replacement: Each result element is the original string with replacements
    2. Count limiting: If count[i] >= 0, at most count[i] replacements are made
    3. Complete replacement: If count[i] < 0, all occurrences are replaced
    4. Identity preservation: If old[i] doesn't occur in a[i], result[i] = a[i]
    5. Zero count behavior: If count[i] = 0, no replacements occur
-/
theorem replace_spec {n : Nat} (a : Vector String n) (old : Vector String n) (new : Vector String n) (count : Vector Int n) :
    ⦃⌜∀ i : Fin n, count.get i = 0 ∨ old.get i ≠ ""⌝⦄
    replace a old new count
    ⦃⇓result => ⌜∀ i : Fin n,
      -- Zero count behavior: if count is 0, no replacements occur
      (count.get i = 0 → result.get i = a.get i) ∧
      -- Identity property: if old doesn't occur, result equals original
      ((∀ pos : Nat, pos + (old.get i).length ≤ (a.get i).length → 
        ¬(((a.get i).drop pos).take (old.get i).length = old.get i)) → 
        result.get i = a.get i) ∧
      -- Basic replacement property: result contains the transformed string
      (∃ (num_replacements : Nat),
        -- Number of replacements is bounded by count (if non-negative)
        (count.get i ≥ 0 → num_replacements ≤ Int.natAbs (count.get i)) ∧
        -- If count is negative, all possible non-overlapping occurrences are replaced
        (count.get i < 0 → 
          ∃ positions : List Nat,
            positions.length = num_replacements ∧
            (∀ p ∈ positions, 
              p + (old.get i).length ≤ (a.get i).length ∧
              ((a.get i).drop p).take (old.get i).length = old.get i) ∧
            -- Positions are sorted and non-overlapping
            (positions.Pairwise (· ≤ ·)) ∧
            (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
              positions[j]! + (old.get i).length ≤ positions[k]!)) ∧
        -- If count is non-negative, we replace min(count, total_occurrences)
        (count.get i ≥ 0 → 
          ∃ total_occurrences : Nat,
            num_replacements = min (Int.natAbs (count.get i)) total_occurrences ∧
            (∃ positions : List Nat,
              positions.length = total_occurrences ∧
              (∀ p ∈ positions, 
                p + (old.get i).length ≤ (a.get i).length ∧
                ((a.get i).drop p).take (old.get i).length = old.get i) ∧
              -- Positions are sorted and non-overlapping
              (positions.Pairwise (· ≤ ·)) ∧
              (∀ j k : Nat, j < k → j < positions.length → k < positions.length →
                positions[j]! + (old.get i).length ≤ positions[k]!))))
    ⌝⦄ := by
  sorry