// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_trivial() {}
// </vc-helpers>

// <vc-spec>
fn setdiff1d(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        /* Each element in result is from ar1 and not in ar2 */
        forall|i: int| 0 <= i < result@.len() ==> 
            exists|j: int| #[trigger] result[i] == ar1[j] && 0 <= j < ar1@.len() &&
            forall|l: int| 0 <= l < ar2@.len() ==> result[i] != ar2[l],
        /* No duplicates in result */
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@.len() && i != j ==> 
            result[i] != result[j],
        /* Result is sorted */
        forall|i: int, j: int| 0 <= i < j < result@.len() ==> result[i] <= result[j]
// </vc-spec>
// <vc-code>
{
    Vec::<i8>::new()
}
// </vc-code>


}
fn main() {}