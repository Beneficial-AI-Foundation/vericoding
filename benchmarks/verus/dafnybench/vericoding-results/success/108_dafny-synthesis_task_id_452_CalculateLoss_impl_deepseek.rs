use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn nonnegative_loss_lemma(cost_price: int, selling_price: int)
    requires
        cost_price >= 0,
        selling_price >= 0,
    ensures
        cost_price >= selling_price ==> cost_price - selling_price >= 0,
        cost_price <= selling_price ==> 0 >= 0,
{
    if cost_price >= selling_price {
        assert(cost_price - selling_price >= 0);
    }
    assert(0 >= 0);
}

proof fn loss_properties_lemma(cost_price: int, selling_price: int, loss: int)
    requires
        cost_price >= 0,
        selling_price >= 0,
        loss == (if cost_price > selling_price { cost_price - selling_price } else { 0 }),
    ensures
        (cost_price > selling_price ==> loss == cost_price - selling_price) && 
        (cost_price <= selling_price ==> loss == 0),
{
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
fn calculate_loss(cost_price: i32, selling_price: i32) -> (loss: i32)
    requires cost_price >= 0 && selling_price >= 0,
    ensures (cost_price > selling_price ==> loss == cost_price - selling_price) && (cost_price <= selling_price ==> loss == 0),
// </vc-spec>
// <vc-code>
{
    proof {
        nonnegative_loss_lemma(cost_price as int, selling_price as int);
    }
    
    let loss = if cost_price > selling_price {
        cost_price - selling_price
    } else {
        0
    };
    
    proof {
        loss_properties_lemma(cost_price as int, selling_price as int, loss as int);
    }
    
    loss
}
// </vc-code>
// </vc-code>

fn main() {
}

}