// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed indexing on vectors by changing `@` to `[]`. */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == (x1[j] & x2[j]),
            forall|k: int| 0 <= k < i ==> ( (x1[k] & x2[k]) == (x2[k] & x1[k]) && (x1[k] & 0) == 0 && (x1[k] & x1[k]) == x1[k] && ((x1[k] & x2[k]) <= x1[k]) && ((x1[k] & x2[k]) <= x2[k]) ),
        decreases x1.len() - i,
    {
        result.push(x1[i] & x2[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}