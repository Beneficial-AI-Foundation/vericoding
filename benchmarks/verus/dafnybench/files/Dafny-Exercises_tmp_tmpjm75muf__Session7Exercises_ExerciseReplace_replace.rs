// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn replace(v: &mut Vec<i8>, x: i8, y: i8)
    ensures
        forall|k: int| 0 <= k < old(v)@.len() && old(v)@[k] == x as int ==> v@[k] == y as int,
        forall|k: int| 0 <= k < old(v)@.len() && old(v)@[k] != x as int ==> v@[k] == old(v)@[k],
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}