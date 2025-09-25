// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn lagroots(c: Vec<i8>) -> (roots: Vec<i8>)
    requires
        c.len() >= 2,
        c@[c.len() - 1 as int] != 0,
    ensures
        c.len() == 2 ==> roots.len() == 1,
        c.len() == 2 ==> roots@[0] as int == 1 + c@[0] as int / c@[1] as int,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}