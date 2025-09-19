// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn find_min_fx(b: i32, c: i32) -> (result: i32)
    requires 
        1 <= b && b <= 20,
        1 <= c && c <= 20,
    ensures 
        result > 0,
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