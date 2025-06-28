use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn CalculateLoss(cost_price: int, selling_price: int) -> (loss: int)
    requires
        cost_price >= 0 && selling_price >= 0
    ensures
        (cost_price > selling_price ==> loss == cost_price - selling_price) && (cost_price <= selling_price ==> loss == 0)
{
    let loss = if cost_price > selling_price {
        cost_price - selling_price
    } else {
        0
    };
    loss
}

}