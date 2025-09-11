// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn hermeadd(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            let coeff1 = if i < c1.len() { c1[i] } else { 0 };
            let coeff2 = if i < c2.len() { c2[i] } else { 0 };
            #[trigger] result[i] == coeff1 + coeff2
        }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}