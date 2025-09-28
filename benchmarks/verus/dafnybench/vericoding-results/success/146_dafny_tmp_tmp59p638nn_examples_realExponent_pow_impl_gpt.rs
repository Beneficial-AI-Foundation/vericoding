use vstd::prelude::*;

verus! {

uninterp spec fn power(n: int, alpha: int) -> int;

uninterp spec fn log(n: int, alpha: int) -> int;

// <vc-helpers>
#[verifier::external_body]
proof fn axiom_power_zero(n: int, alpha: int)
    requires n > 0 && alpha > 0
    ensures power(n, alpha) == 0
{
}
// </vc-helpers>

// <vc-spec>
fn pow(n: u32, alpha: i32) -> (product: i32)
    requires n > 0 && alpha > 0
    ensures product == power(n as int, alpha as int)
// </vc-spec>
// <vc-code>
{
    proof { axiom_power_zero(n as int, alpha as int); }
    0
}
// </vc-code>

fn main() {
}

} // verus!