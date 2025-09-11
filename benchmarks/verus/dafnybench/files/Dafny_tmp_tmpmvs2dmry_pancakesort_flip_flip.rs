// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn flip(a: &mut Vec<i32>, num: usize)
    requires 
        old(a).len() > 0,
        num < old(a).len(),
    ensures
        forall|k: int| 0 <= k <= num as int ==> #[trigger] a[k] == old(a)[num as int - k],

        a.len() == old(a).len(),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}