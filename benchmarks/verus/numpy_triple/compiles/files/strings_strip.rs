/* 
{
  "name": "numpy.strings.strip",
  "category": "String operations",
  "description": "For each element in a, return a copy with the leading and trailing characters removed",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.strings.strip.html",
  "doc": "For each element in `a`, return a copy with the leading and trailing characters removed.\n\nParameters\n----------\na : array_like, with `StringDType`, `bytes_` or `str_` dtype\nchars : array_like with `StringDType`, `bytes_` or `str_` dtype, optional\n    The characters to be removed. If None, whitespace characters are removed.\n\nReturns\n-------\nout : ndarray\n    Output array of `StringDType`, `bytes_` or `str_` dtype,\n    depending on input types",
}
*/

/* numpy.strings.strip: For each element in a vector, return a copy with the leading and trailing characters removed.

   Removes both leading and trailing characters from each string element in the input vector.
   This is a combination of lstrip and rstrip operations. The behavior depends on the chars parameter:
   - If chars is None, whitespace characters are removed from both ends
   - If chars is provided, any combination of those characters is removed from both ends
   
   The function preserves the shape of the input array and handles empty strings
   appropriately by returning them unchanged.

   From NumPy documentation:
   - Parameters: a (array_like) - Input array with string dtype
                 chars (optional) - Characters to remove from both ends
   - Returns: out (ndarray) - Output array with leading and trailing characters removed

   Mathematical Properties:
   1. Element-wise transformation: result[i] = strip(a[i], chars) for all i
   2. Length preservation or reduction: result[i].length ≤ a[i].length for all i
   3. Substring property: result[i] is a substring of a[i] for all i
   4. Character set removal: only characters in chars are removed from both ends
   5. Preserves vector length: result.size = a.size
   6. Combination of lstrip and rstrip: strip(s) = rstrip(lstrip(s))
*/

/* Specification: numpy.strings.strip returns a vector where each string element
   has its leading and trailing characters removed according to the chars parameter.

   Mathematical Properties:
   1. Element-wise correctness: Each element is correctly processed for both leading and trailing character removal
   2. Length preservation or reduction: Each result string is no longer than the original
   3. Substring property: Each result is a substring of the original string
   4. Character set stripping: Only characters in chars are removed from both ends
   5. Whitespace default: When chars is None, whitespace characters are removed
   6. Maximal stripping: Remove as many characters as possible from both ends
   7. Empty string handling: Empty strings remain empty
   8. Middle preservation: Characters in the middle of the string are unchanged
   9. Composition property: strip combines lstrip and rstrip functionality
   10. Idempotent-like property: applying strip to result with same chars removes nothing

   Precondition: True (no special preconditions for strip)
   Postcondition: For all indices i, result[i] is a[i] with leading and trailing characters removed
*/
use vstd::prelude::*;

verus! {
/* <vc-helpers> */
/* </vc-helpers> */
fn strip(a: Vec<String>, chars: Option<String>) -> (result: Vec<String>)
    requires true
/* <vc-implementation> */
    {
        return Vec::<String>::new(); // TODO: Remove this line and implement the function body
    }
/* </vc-implementation> */
proof fn strip_spec(a: Vec<String>, chars: Option<String>)
/* <vc-proof> */
    {
        assume(false); // TODO: Remove this line and implement the proof
    }
/* </vc-proof> */
fn main() {}

}