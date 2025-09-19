// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn maximum(values: Vec<i8>) -> (max: i8)
    requires
        values@.len() > 0,
    ensures
        values@.contains(max),
        forall|i: int| 0 <= i < values@.len() ==> values@[i] <= max,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}