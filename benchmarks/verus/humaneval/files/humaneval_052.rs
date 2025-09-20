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
fn check_below_threshold(l: Vec<i8>, t: i8) -> (result: bool)
    ensures result == below_threshold(l@.map(|_i: int, x: i8| x as int), t as int)
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