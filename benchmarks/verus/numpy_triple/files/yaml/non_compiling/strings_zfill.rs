/* numpy.strings.zfill: Return the numeric string left-filled with zeros.

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
5. Minimality: no over-padding beyond required width */

use vstd::prelude::*;

verus! {
fn zfill(a: Vec<String>, width: usize) -> (result: Vec<String>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> {
            let original = a[i];
            let res = result[i];
            /* Length invariant: result length is exactly max(orig.length, width) */
            res.len() == if original.len() >= width { original.len() } else { width } &&
            /* Identity morphism: strings already >= width are unchanged */
            (original.len() >= width ==> res == original) &&
            /* Zero-padding for short strings without signs */
            (original.len() < width && original.len() > 0 && 
             !original.starts_with("+") && !original.starts_with("-") ==>
               exists|padding: String| res == padding + original &&
               padding.len() == width - original.len() &&
               forall|j: int| 0 <= j < padding.len() ==> padding.chars().nth(j as usize) == Some('0')) &&
            /* Sign preservation: leading '+' or '-' are preserved at start */
            (original.len() < width && original.len() > 0 && 
             (original.starts_with("+") || original.starts_with("-")) ==>
               exists|sign: char, rest: String, padding: String|
                 (sign == '+' || sign == '-') &&
                 original.chars().nth(0) == Some(sign) &&
                 res.len() == width &&
                 res.starts_with(&sign.to_string()) &&
                 padding.len() == width - original.len()) &&
            /* Empty string handling: empty strings become all zeros */
            (original.len() == 0 ==> 
               res.len() == width && 
               forall|j: int| 0 <= j < width ==> res.chars().nth(j as usize) == Some('0')) &&
            /* Exactness constraint: padding achieves exact width requirement */
            (original.len() < width ==> res.len() == width)
        }
{
    // impl-start
    assume(false);
    Vec::new()
    // impl-end
}
}
fn main() {}