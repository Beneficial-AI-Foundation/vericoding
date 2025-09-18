// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed previously added declaration of `bitwise_or` as there should be only one declaration. */
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
/* code modified by LLM (iteration 5): Added `i as nat` for calls to `get` which expects `usize` argument. */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant 
            0 <= i as int && i as int <= x1.len(),
            result.len() == i as nat,
            forall|j: int| 0 <= j && j < i as int ==> result[j] == (x1@[j] | x2@[j]),
    {
        let val = x1.get(i as nat).unwrap() | x2.get(i as nat).unwrap();
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}