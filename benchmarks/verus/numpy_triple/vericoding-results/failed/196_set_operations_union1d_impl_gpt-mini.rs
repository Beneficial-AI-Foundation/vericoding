// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute index in 0..256 and round-trip property */
fn to_index(x: i8) -> usize
    ensures
        result < 256,
        ((result as int) - 128) as i8 == x,
{
    ((x as int) + 128) as usize
}
// </vc-helpers>

// <vc-spec>
fn union1d(ar1: Vec<i8>, ar2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        /* Union property: every element from either input array is in result */
        forall|i: int| 0 <= i < ar1.len() ==> 
            #[trigger] result@.contains(ar1[i]),
        forall|i: int| 0 <= i < ar2.len() ==> 
            #[trigger] result@.contains(ar2[i]),
        /* Completeness: every element in result comes from one of the input arrays */
        forall|j: int| 0 <= j < result.len() ==> 
            ar1@.contains(result[j]) || ar2@.contains(result[j]),
        /* Sorted property: result is sorted in ascending order */
        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            #[trigger] result[i] <= #[trigger] result[j],
        /* Uniqueness property: no duplicate elements */
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && i != j ==> 
            #[trigger] result[i] != #[trigger] result[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build sorted unique union by scanning all 256 i8 values and pushing those present in ar1 or ar2, tracking their source index for proofs */
    let mut result: Vec<i8> = Vec::<i8>::new();
    let mut idxs: Vec<usize> = Vec::<usize>::new();
    let mut v: usize = 0;
    while v < 256
        invariant
            v <= 256,
            result.len() == idxs.len(),
            forall|p: int| 0 <= p < result.len() ==> ar1@.contains(result[p]) || ar2@.contains(result[p]),
            forall|p: int| 0 <= p < result.len() ==> result[p] == ((idxs[p] as int) - 128) as i8,
            forall|p: int, q: int| 0 <= p < q < idxs.len() ==> idxs[p] < idxs[q],
            forall|p: int| 0 <= p < idxs.len() ==> 0 <= idxs[p] < v,
        decreases
            256 - v,
    {
        let val: i8 = ((v as int) - 128) as i8;
        if ar1@.contains(val) || ar2@.contains(val) {
            result.push(val);
            idxs.push(v);
        }
        v += 1;
    }

    result
}
// </vc-code>


}
fn main() {}