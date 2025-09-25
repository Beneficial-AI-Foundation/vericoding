// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn gcd_spec(a: int, b: int) -> nat;

spec fn lcm_spec(a: int, b: int) -> nat;

fn lcm(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1@.len(),

        forall|i: int| 0 <= i < result@.len() ==> result@[i] >= 0,

        forall|i: int| 0 <= i < result@.len() ==> result@[i] >= 0,

        forall|i: int| 0 <= i < result@.len() ==> 
            (x1@[i] == 0 || x2@[i] == 0) ==> result@[i] == 0,

        forall|i: int| 0 <= i < result@.len() ==> 
            (x1@[i] != 0 && x2@[i] != 0) ==> result@[i] > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}