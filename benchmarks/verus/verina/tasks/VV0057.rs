// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn nth_ugly_number(n: u32) -> (result: u32)
    requires n > 0,
    ensures result > 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}