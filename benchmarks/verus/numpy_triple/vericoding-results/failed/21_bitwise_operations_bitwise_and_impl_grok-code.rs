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
    /* code modified by LLM (iteration 5): Fixed type mismatch in forall quantifier by changing j from nat to int to match sequence indexing expectations. */
    let len = x1.len();
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i,
            forall |j: int| #![auto] 0 <= j < i ==> result@[j] == x1@[j] & x2@[j]
        decreases (len - i)
    {
        proof { assert(i < x1.len()); }
        proof { assert(i < x2.len()); }
        let val1 = x1[i];
        let val2 = x2[i];
        let val = val1 & val2;
        result.push(val);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}