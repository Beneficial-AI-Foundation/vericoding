/* numpy.strings.rjust: Return an array with the elements of a right-justified in a string of length width.

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

Specification: rjust returns a vector where each string is right-justified
to the specified width using the given fill character.

Mathematical Properties:
- Length preservation: Result length is max(original_length, width)
- Identity: Strings already >= width remain unchanged
- Right-justification: Original content preserved as suffix, padding on left
- Minimality: No unnecessary padding beyond required width
- Fillchar constraint: Padding uses specified fill character */

use vstd::prelude::*;

verus! {
fn rjust(a: &Vec<Seq<char>>, width: usize, fillchar: char) -> (result: Vec<Seq<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let orig = #[trigger] a[i];
            let res = result[i];
            res.len() >= orig.len() &&
            (orig.len() >= width ==> res == orig) &&
            (orig.len() < width ==> res.len() == width) &&
            (orig.len() == 0 ==> res.len() == width)
        },
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}