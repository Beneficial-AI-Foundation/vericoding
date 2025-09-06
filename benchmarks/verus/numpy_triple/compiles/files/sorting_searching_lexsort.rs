/* 
{
  "name": "numpy.lexsort",
  "category": "Sorting",
  "description": "Perform an indirect stable sort using a sequence of keys",
  "url": "https://numpy.org/doc/stable/reference/generated/numpy.lexsort.html",
  "doc": "Perform an indirect stable sort using a sequence of keys.\n\nGiven multiple sorting keys, which can be interpreted as columns in a\nspreadsheet, lexsort returns an array of integer indices that describes\nthe sort order by multiple columns. The last key in the sequence is used\nfor the primary sort order, ties are broken by the second-to-last key,\nand so on.\n\nParameters\n----------\nkeys : (k, N) array or tuple containing k (N,)-shaped sequences\n    The `k` different \"columns\" to be sorted. The last column (or row if\n    `keys` is a 2D array) is the primary sort key.\naxis : int, optional\n    Axis to be indirectly sorted. By default, sort over the last axis.\n\nReturns\n-------\nindices : (N,) ndarray of ints\n    Array of indices that sort the keys along the specified axis.\n\nNote\n----\nThe Numpy lexsort function treats keys as column vectors and sorts by the last key\n(primary key) first. This can be counterintuitive coming from other languages.",
}
*/

/* Perform an indirect stable sort using a sequence of keys.
   Given multiple sorting keys, lexsort returns an array of integer indices that 
   describes the sort order by multiple columns. The last key in the sequence is used
   for the primary sort order, ties are broken by the second-to-last key, and so on. */

/* Specification: lexsort returns indices that lexicographically sort the keys.
   The result is a permutation of indices where for any two positions i, j:
   - If primary key differs, sort by primary key
   - If primary key is equal, sort by second-to-last key, etc.
   - The sort is stable (preserves relative order of equal elements) */
use vstd::prelude::*;

verus! {
// <vc-helpers>
// </vc-helpers>
fn lexsort(keys: Vec<Vec<i32>>, n: usize, k: usize) -> (result: Vec<usize>)
    requires
        k > 0,
        keys.len() == k,
        forall|i: int| #![auto] 0 <= i < k ==> keys[i].len() == n,
    ensures
        result.len() == n,
// <vc-implementation>
{
    let mut result = Vec::new();
    let mut idx = 0;
    while idx < n
        invariant 
            result.len() == idx,
            idx <= n,
        decreases n - idx
    {
        result.push(0);
        idx += 1;
    }
    return result; // TODO: Remove this line and implement the function body
}
// </vc-implementation>
proof fn lexsort_spec(keys: Vec<Vec<i32>>, n: usize, k: usize)
    requires
        k > 0,
        keys.len() == k,
        forall|i: int| #![auto] 0 <= i < k ==> keys[i].len() == n,
    ensures
        true,
// <vc-proof>
{
    assume(false); // TODO: Remove this line and implement the proof
}
// </vc-proof>
fn main() {
}

}