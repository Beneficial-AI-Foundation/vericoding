use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn calculate_loss(cost_price: i32, selling_price: i32) -> (loss: i32)
    requires cost_price >= 0 && selling_price >= 0,
    ensures (cost_price > selling_price ==> loss == cost_price - selling_price) && (cost_price <= selling_price ==> loss == 0),
// </vc-spec>
// <vc-code>
{
    if cost_price > selling_price {
        let loss = cost_price - selling_price;
        assert(cost_price > selling_price);
        assert(loss == cost_price - selling_price);
        loss
    } else {
        assert(cost_price <= selling_price);
        0
    }
}
// </vc-code>

fn main() {
}

}