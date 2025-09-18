// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed duplicate spec and lemma declarations */
// </vc-helpers>

// <vc-spec>
spec fn bitwise_or(x: i32, y: i32) -> i32;

proof fn bitwise_or_comm(x: i32, y: i32)
    ensures bitwise_or(x, y) == bitwise_or(y, x)
{
    assume(false);
}

proof fn bitwise_or_zero(x: i32)
    ensures bitwise_or(x, 0) == x
{
    assume(false);
}

proof fn bitwise_or_idempotent(x: i32)
    ensures bitwise_or(x, x) == x
{
    assume(false);
}

fn numpy_bitwise_or(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == bitwise_or(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i], x2[i]) == bitwise_or(x2[i], x1[i]),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i], 0) == x1[i],
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i], x1[i]) == x1[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation by removing duplicate specifications */
{
    let len = x1.len();
    let mut result = Vec::with_capacity(len);
    let mut n = 0;
    
    while n < len
        invariant
            0 <= n <= len,
            result.len() == n,
            forall|i: int| 0 <= i < n ==> result[i] == bitwise_or(x1[i], x2[i]),
            forall|i: int| 0 <= i < n ==> bitwise_or(x1[i], x2[i]) == bitwise_or(x2[i], x1[i]),
            forall|i: int| 0 <= i < n ==> bitwise_or(x1[i], 0) == x1[i],
            forall|i: int| 0 <= i < n ==> bitwise_or(x1[i], x1[i]) == x1[i],
        decreases len - n
    {
        let x1_val = x1[n];
        let x2_val = x2[n];
        let or_result = x1_val | x2_val;
        result.push(or_result);
        n = n + 1;
    }
    result
}
// </vc-code>

}
fn main() {}