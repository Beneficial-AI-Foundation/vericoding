// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_floor(x: Vec<i32>) -> (result: Vec<i32>)
    requires x.len() > 0,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x[i],
        forall|i: int| 0 <= i < result.len() ==> x[i] < result[i] + 1,
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result.len() && x[i] <= x[j] ==> result[i] <= result[j],
        forall|i: int| 0 <= i < result.len() ==> result[i] == x[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to fix verification error */
    let mut result: Vec<i32> = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] <= x[j],
            forall|j: int| 0 <= j < i ==> x[j] < result[j] + 1,
            forall|j: int, k: int| 0 <= j < i && 0 <= k < i && x[j] <= x[k] ==> result[j] <= result[k],
            forall|j: int| 0 <= j < i ==> result[j] == x[j],
        decreases x.len() - i
    {
        result.push(x[i]);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}