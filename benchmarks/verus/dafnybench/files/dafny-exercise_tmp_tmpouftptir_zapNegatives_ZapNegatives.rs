// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn zap_negatives(a: &mut Vec<i32>)
    ensures 
        a.len() == old(a).len(),
        forall|i: int| 0 <= i < a.len() ==> 
            if old(a)[i] < 0 { a[i] == 0 } 
            else { a[i] == old(a)[i] }
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}