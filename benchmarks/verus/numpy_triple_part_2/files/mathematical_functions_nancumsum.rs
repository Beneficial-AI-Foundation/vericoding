// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nancumsum(a: Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        a.len() > 0 ==> (result[0] == a[0]),
        forall|i: int| 0 < i < result.len() ==> result[i] == result[i-1] + a[i],
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