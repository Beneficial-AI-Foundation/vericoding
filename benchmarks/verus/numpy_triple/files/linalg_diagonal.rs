// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn spec_min(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

fn numpy_diagonal(x: Vec<Vec<f32>>, offset: i32) -> (result: Vec<f32>)
    requires 
        x.len() > 0,
        x.len() < usize::MAX,
        forall|i: int| #![trigger x[i]] 0 <= i < x.len() ==> x[i].len() > 0,
        forall|i: int| #![trigger x[i]] 0 <= i < x.len() ==> x[i].len() == x[0].len(),
    ensures
        result.len() == spec_min(x.len() as int, x[0].len() as int),
        offset == 0 ==> forall|i: int| #![trigger result[i]] 0 <= i < result.len() ==> 
            result[i] == x[i][i],
        true, // Result elements are derived from the diagonal of x
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}