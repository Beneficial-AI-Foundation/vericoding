// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagmulx(c: Vec<i32>) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures 
        result.len() == c.len() + 1,
        result[0] == c[0],
        result.len() >= 2 ==> result[1] == -c[0]
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