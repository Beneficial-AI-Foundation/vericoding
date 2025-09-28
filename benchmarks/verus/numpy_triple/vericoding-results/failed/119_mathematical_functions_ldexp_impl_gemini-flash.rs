// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Removed `ldexp_value` definition to avoid duplication, as it is already defined in `<vc-spec>` */

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
    /* code modified by LLM (iteration 5): Fixed compilation error by replacing `x1.index()` and `x2.index()` with `x1[i]` and `x2[i]` respectively, as `view_nth` is used in the invariant */
    let mut result: Vec<f32> = Vec::new();
    let mut i: int = 0;
    while i < x1.len()
        invariant
            0 <= i,
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result.view_nth(j) == ldexp_value(x1.view_nth(j), x2.view_nth(j)),
        decreases x1.len() - i
    {
        result.push(ldexp_value(x1[i], x2[i]));
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}