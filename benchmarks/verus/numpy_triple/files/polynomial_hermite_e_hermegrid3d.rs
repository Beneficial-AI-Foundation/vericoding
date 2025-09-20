// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn hermite_e_poly(x: int, n: nat) -> int
    decreases n
{
    if n == 0 {
        1
    } else if n == 1 {
        x
    } else {
        x * hermite_e_poly(x, (n - 1) as nat) - (n - 1) * hermite_e_poly(x, (n - 2) as nat)
    }
}

fn hermegrid3d(x: Vec<f32>, y: Vec<f32>, z: Vec<f32>, c: Vec<Vec<Vec<f32>>>) -> (result: Vec<Vec<Vec<f32>>>)
    requires
        x.len() > 0,
        y.len() > 0,
        z.len() > 0,
        c.len() > 0,
        forall|i: int| 0 <= i < c@.len() ==> c@[i].len() > 0,
        forall|i: int, j: int| 0 <= i < c@.len() && 0 <= j < c@[i].len() ==> c@[i][j].len() > 0,
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result@.len() ==> result@[i].len() == y.len(),
        forall|i: int, j: int| 0 <= i < result@.len() && 0 <= j < result@[i].len() ==> result@[i][j].len() == z.len(),
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}