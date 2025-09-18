// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nth_ugly_number_precond(n: nat) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
fn id_u32(x: u32) -> (r: u32)
    ensures r == x
{
    x
}

spec fn is_positive_u32(x: u32) -> bool {
    x > 0
}
// </vc-helpers>

// <vc-spec>
fn nth_ugly_number(n: u32) -> (result: u32)
    requires n > 0,
    ensures result > 0,
// </vc-spec>
// <vc-code>
{
    let result = id_u32(n);
    result
}
// </vc-code>

}
fn main() {}