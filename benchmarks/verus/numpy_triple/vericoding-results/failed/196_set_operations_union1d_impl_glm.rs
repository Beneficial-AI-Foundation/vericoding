// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn i8_to_index(x: i8) -> (index: usize)
    requires
        -128 <= x <= 127,
    ensures
        0 <= index < 256,
{
    /* helper modified by LLM (iteration 5): fixed conversion bounds */
    (x as isize + 128) as usize
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
    /* code modified by LLM (iteration 5): fixed type mismatches in quantifiers */
    let mut combined = ar1;
    combined.extend(ar2);
    let mut seen = [false; 256];
    let mut result: Vec<i8> = Vec::new();
    let mut index = 0;
    while index < combined.len()
        invariant
            0 <= index <= combined.len(),
            forall|j: int| -128 <= j <= 127 ==> 
                (seen[i8_to_index(j as i8)] <==> result@.contains(j as i8)),
            forall|j: i8| result@.contains(j) ==> 
                exists|k: int| 0 <= k < index && combined[k] == j,
        decreases combined.len() - index,
    {
        let elem = combined[index];
        let idx = i8_to_index(elem);
        if !seen[idx] {
            seen[idx] = true;
            result.push(elem);
        }
        index += 1;
    }

    result.sort();
    result
}
// </vc-code>


}
fn main() {}