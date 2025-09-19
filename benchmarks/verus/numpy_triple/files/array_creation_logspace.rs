// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn logspace(start: i8, stop: i8, endpoint: bool, base: i8, num: usize) -> (result: Vec<i8>)
    requires 
        base as int > 0,
        base as int != 1,
        num > 0,
    ensures
        result.len() == num,
        forall|i: int| 0 <= i < num ==> result@[i] as int > 0,
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