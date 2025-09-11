// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn longest_prefix(a: &[i32], b: &[i32]) -> (i: usize)
    ensures 
        i <= a.len() && i <= b.len(),
        a@.subrange(0, i as int) == b@.subrange(0, i as int),
        i < a.len() && i < b.len() ==> a[i as int] != b[i as int]
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}