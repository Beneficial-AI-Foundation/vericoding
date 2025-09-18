// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define concrete body for bitwise_or using built-in bitwise OR */
spec fn bitwise_or(x: i32, y: i32) -> i32 { x | y }
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
{
    /* code modified by LLM (iteration 5): compute elementwise OR using concrete spec body; maintain invariant relating exec vector to spec */
    let n = x1.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            x1.len() == n,
            x2.len() == n,
            i <= n,
            out.len() == i,
            forall|j: int| 0 <= j && j < i as int implies out@[j] == bitwise_or(x1@[j], x2@[j])
        decreases (n as int) - (i as int)
    {
        let xi = x1[i];
        let yi = x2[i];
        let ri = xi | yi;
        out.push(ri);
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j && j < out.len() implies out[j] == bitwise_or(x1[j], x2[j]) by { };
        assert forall|j: int| 0 <= j && j < out.len() implies bitwise_or(x1[j], x2[j]) == bitwise_or(x2[j], x1[j]) by { };
        assert forall|j: int| 0 <= j && j < out.len() implies bitwise_or(x1[j], 0) == x1[j] by { };
        assert forall|j: int| 0 <= j && j < out.len() implies bitwise_or(x1[j], x1[j]) == x1[j] by { };
    }
    out
}
// </vc-code>

}
fn main() {}