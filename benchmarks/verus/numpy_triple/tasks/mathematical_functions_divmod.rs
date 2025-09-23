// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn divmod(x1: Vec<i8>, x2: Vec<i8>) -> (result: (Vec<i8>, Vec<i8>))
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x2.len() ==> x2[i] != 0,
    ensures ({
        let (quotient, remainder) = result;
        &&& quotient.len() == x1.len()
        &&& remainder.len() == x1.len()
        &&& forall|i: int| 0 <= i < x1.len() ==> 
            x1[i] as int == x2[i] as int * quotient[i] as int + remainder[i] as int
    })
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}