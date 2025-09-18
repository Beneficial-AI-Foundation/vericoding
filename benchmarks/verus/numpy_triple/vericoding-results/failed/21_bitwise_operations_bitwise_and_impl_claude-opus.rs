// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix type errors by using proper indexing */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x1@[j] & x2@[j]),
            forall|j: int| 0 <= j < i ==> result@[j] >= 0,
            forall|j: int| 0 <= j < i ==> result@[j] <= x1@[j],
            forall|j: int| 0 <= j < i ==> result@[j] <= x2@[j],
            forall|j: int| 0 <= j < i ==> (result@[j] == 0 <==> (x1@[j] == 0 || x2@[j] == 0)),
            forall|j: int| 0 <= j < i ==> (x1@[j] == x2@[j] ==> result@[j] == x1@[j]),
        decreases x1.len() - i
    {
        let val = x1[i] & x2[i];
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}