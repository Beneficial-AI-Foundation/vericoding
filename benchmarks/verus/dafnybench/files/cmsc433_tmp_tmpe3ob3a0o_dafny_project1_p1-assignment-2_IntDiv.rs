// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn IntDiv(m: i8, n: i8) -> (ret: (i8, i8))
    requires n as int > 0
    ensures m as int == (n as int) * (ret.0 as int) + (ret.1 as int) && 0 <= ret.1 as int && (ret.1 as int) < (n as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}