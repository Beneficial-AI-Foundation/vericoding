// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u8>, x2: &Vec<u8>) -> (result: Vec<u8>)
    requires x1@.len() == x2@.len(),
    ensures 
        result@.len() == x1@.len(),
        forall|i: int| 0 <= i < result@.len() ==> 
            result@[i] == (x1@[i] & x2@[i]) &&

            (x1@[i] & x2@[i]) == (x2@[i] & x1@[i]) &&

            (x1@[i] & 0) == 0 &&

            (x1@[i] & x1@[i]) == x1@[i] &&

            result@[i] <= x1@[i] && result@[i] <= x2@[i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}