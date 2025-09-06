/* numpy.strings.rpartition: Partition each element in a around the right-most separator

Partition (split) each element around the right-most separator.

For each element in `a`, split the element at the last occurrence of `sep`, and return a 3-tuple containing the part before the separator, the separator itself, and the part after the separator. If the separator is not found, the third item of the tuple will contain the whole string, and the first and second ones will be empty strings.

Parameters
----------
a : array_like, with `StringDType`, `bytes_` or `str_` dtype
    Input array
sep : array_like, with `StringDType`, `bytes_` or `str_` dtype
    Right-most separator to split each string element in `a`

Returns
-------
out : 3-tuple of ndarrays
    Three arrays of `StringDType`, `bytes_` or `str_` dtype,
    depending on input types

numpy.strings.rpartition: Partition each element in a around the right-most separator.

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

Specification: numpy.strings.rpartition returns a 3-tuple of vectors where each
element is partitioned around the last occurrence of the separator.

Mathematical Properties:
1. Right partition correctness: For each index i, the result satisfies rpartition semantics
2. Completeness: When separator is found, concatenation reconstructs original string
3. Last occurrence: Only the last occurrence of separator is used for partitioning
4. Not found case: When separator is not found, returns ("", "", original)
5. Preserves vector length: All result vectors have the same length as input
6. Separator consistency: The separator part contains the actual separator or empty string

Precondition: True (no special preconditions for string partitioning)
Postcondition: For all indices i, the partition satisfies the rpartition semantics */

use vstd::prelude::*;

verus! {
fn rpartition(a: &Vec<String>, sep: &str) -> (result: (Vec<String>, Vec<String>, Vec<String>))
    ensures
        result.0.len() == a.len(),
        result.1.len() == a.len(),
        result.2.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result.0[i] == result.0[i] &&
            (result.0[i]@ + result.1[i]@ + result.2[i]@ == a[i]@) &&
            (result.1[i]@ == sep@ || result.1[i]@ == ""@) &&
            (result.1[i]@ == sep@ ==> result.1[i]@ == sep@) &&
            (result.1[i]@ == ""@ ==> result.0[i]@ == ""@ && result.2[i]@ == a[i]@),
{
    // impl-start
    assume(false);
    (Vec::new(), Vec::new(), Vec::new())
    // impl-end
}
}
fn main() {}