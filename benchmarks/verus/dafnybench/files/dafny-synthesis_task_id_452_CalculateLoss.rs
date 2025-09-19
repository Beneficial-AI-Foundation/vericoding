// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate_loss(cost_price: i8, selling_price: i8) -> (loss: i8)
    requires cost_price >= 0 && selling_price >= 0,
    ensures (cost_price as int > selling_price as int ==> loss as int == cost_price as int - selling_price as int) && (cost_price as int <= selling_price as int ==> loss as int == 0),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}