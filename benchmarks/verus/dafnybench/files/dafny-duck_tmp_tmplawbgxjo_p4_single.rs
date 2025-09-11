// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn single(x: &[i32], y: &[i32]) -> (b: Vec<i32>)
    requires 
        x.len() > 0,
        y.len() > 0,
    ensures 
        b@.len() == x@.len() + y@.len(),
        b@ == x@ + y@,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}