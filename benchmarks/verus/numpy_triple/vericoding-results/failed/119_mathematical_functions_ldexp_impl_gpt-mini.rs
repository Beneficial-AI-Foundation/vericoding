// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial placeholder proof for ldexp_value */
proof fn ldexp_value_helper() {
    // No concrete properties to prove for the uninterpreted spec function
}

// </vc-helpers>

// <vc-spec>
spec fn ldexp_value(x1: f32, x2: i32) -> f32;

fn ldexp(x1: Vec<f32>, x2: Vec<i32>) -> (result: Vec<f32>)
    requires x1.len() == x2.len(),
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == ldexp_value(x1[i], x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement using usize indices and maintain invariant */
    let n: usize = x1.len();
    let mut res: Vec<f32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res.len() == i,
            forall |j: usize| j < i ==> res[j] == ldexp_value(x1[j], x2[j]),
        decreases n - i
    {
        let v: f32 = ldexp_value(x1[i], x2[i]);
        res.push(v);
        i = i + 1;
    }
    res
}

// </vc-code>

}
fn main() {}