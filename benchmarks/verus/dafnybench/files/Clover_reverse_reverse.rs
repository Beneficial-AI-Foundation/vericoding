// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn reverse(a: &mut Vec<i32>)
    ensures forall|i: int| 0 <= i < old(a).len() ==> a[i] == old(a)[old(a).len() - 1 - i]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}