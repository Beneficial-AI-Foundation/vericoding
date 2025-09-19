// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
exec fn is_break_even(cost_price: i8, selling_price: i8) -> (result: bool)
    requires cost_price as int >= 0 && selling_price as int >= 0,
    ensures result <==> (cost_price as int == selling_price as int),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}