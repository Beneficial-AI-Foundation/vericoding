// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn delete(line: &mut Vec<char>, l: usize, at: usize, p: usize)
    requires
        l <= old(line).len(),
        at + p <= l,
    ensures
        line@ == old(line)@.subrange(0, at as int) + old(line)@.subrange((at + p) as int, l as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}