use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
exec fn is_break_even(cost_price: int, selling_price: int) -> (result: bool)
    requires cost_price >= 0 && selling_price >= 0,
    ensures result <==> (cost_price == selling_price),
// </vc-spec>
// <vc-code>
{
  cost_price == selling_price
}
// </vc-code>

fn main() {}

}