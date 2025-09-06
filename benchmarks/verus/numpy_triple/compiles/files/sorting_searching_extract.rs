/*
{
  "name": "numpy.extract",
  "category": "Searching", 
  "description": "Return the elements of an array that satisfy some condition",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.extract.html",
  "doc": "Return the elements of an array that satisfy some condition.\n\nThis is equivalent to \`\`np.compress(ravel(condition), ravel(arr))\`\`. If\n\`condition\` is boolean \`\`np.extract\`\` is equivalent to \`\`arr[condition]\`\`.\n\nNote that \`place\` does the exact opposite of \`extract\`.\n\nParameters\n----------\ncondition : array_like\n    An array whose nonzero or True entries indicate the elements of \`arr\`\n    to extract.\narr : array_like\n    Input array of the same size as \`condition\`.\n\nReturns\n-------\nextract : ndarray\n    Rank 1 array of values from \`arr\` where \`condition\` is True.\n\nSee Also\n--------\ntake, put, copyto, compress, place",
}
*/

/* Return the elements of an array that satisfy some condition.
   The result size is the number of True entries in the condition array. */

/* Specification: extract returns elements from arr where condition is True.
   The result contains exactly those elements from arr at positions where condition is True,
   preserving their original order. The result size m equals the number of True values in condition. */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
fn extract(condition: Vec<bool>, arr: Vec<i32>) -> (result: Vec<i32>)
    requires
        condition.len() == arr.len(),
    ensures
        /* Each element in result comes from arr at a position where condition is true */
        forall|k: int| #![trigger result[k]] 0 <= k < result.len() ==> 
            exists|i: int| 0 <= i < condition.len() && condition[i] == true && result[k] == arr[i],
        /* The order is preserved: elements appear in the same relative order as in arr */
        forall|k1: int, k2: int| #![trigger result[k1], result[k2]] 0 <= k1 < k2 < result.len() ==> 
            exists|i1: int, i2: int| 0 <= i1 < i2 < condition.len() && 
            condition[i1] == true && condition[i2] == true &&
            result[k1] == arr[i1] && result[k2] == arr[i2],
        /* Every True position in condition contributes exactly one element to the result */
        forall|i: int| #![trigger condition[i]] 0 <= i < condition.len() && condition[i] == true ==> 
            exists|k: int| 0 <= k < result.len() && result[k] == arr[i],
// <vc-implementation>
    {
        proof {
            assume(false);
        }
        return Vec::new(); // TODO: Remove this line and implement the function body
    }
// </vc-implementation>
proof fn extract_spec(condition: Vec<bool>, arr: Vec<i32>)
    requires
        condition.len() == arr.len(),
// <vc-proof>
    {
        assume(false); // TODO: Remove this line and implement the proof
    }
// </vc-proof>

fn main() {}

}