// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn below_threshold(l: Seq<int>, t: int) -> bool {
    forall|i: int| 0 <= i < l.len() ==> l[i] < t
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn check_below_threshold(l: Seq<int>, t: int) -> (result: bool)
    ensures result == below_threshold(l, t)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}

fn main() {}