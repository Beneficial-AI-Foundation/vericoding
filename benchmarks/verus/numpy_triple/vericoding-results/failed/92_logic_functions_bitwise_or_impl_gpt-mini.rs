// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple noop helper to satisfy helpers section */
proof fn helper_noop()
{
}

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

fn numpy_bitwise_or(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as i32 == bitwise_or(x1[i] as i32, x2[i] as i32),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, x2[i] as i32) == bitwise_or(x2[i] as i32, x1[i] as i32),
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, 0) == x1[i] as i32,
        forall|i: int| 0 <= i < result.len() ==> bitwise_or(x1[i] as i32, x1[i] as i32) == x1[i] as i32,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use Vec.view() and int indices to satisfy preconditions and maintain invariants */
    let n: int = x1.view().len();
    let mut result: Vec<i8> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            result.len() == i as usize,
            forall|k: int| 0 <= k < i ==> result.view()@[k] as i32 == bitwise_or(x1.view()@[k] as i32, x2.view()@[k] as i32),
            forall|k: int| 0 <= k < i ==> bitwise_or(x1.view()@[k] as i32, x2.view()@[k] as i32) == bitwise_or(x2.view()@[k] as i32, x1.view()@[k] as i32),
            forall|k: int| 0 <= k < i ==> bitwise_or(x1.view()@[k] as i32, 0) == x1.view()@[k] as i32,
            forall|k: int| 0 <= k < i ==> bitwise_or(x1.view()@[k] as i32, x1.view()@[k] as i32) == x1.view()@[k] as i32,
        decreases n - i,
    {
        let ai: i8 = x1.view()@[i];
        let bi: i8 = x2.view()@[i];
        let vi: i8 = ai | bi;
        result.push(vi);
        proof {
            assert(result.view()@[i] as i32 == vi as i32);
            assert(result.view()@[i] as i32 == bitwise_or(x1.view()@[i] as i32, x2.view()@[i] as i32));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}