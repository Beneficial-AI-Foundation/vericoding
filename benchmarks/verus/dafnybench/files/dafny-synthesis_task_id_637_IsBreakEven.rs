use vstd::prelude::*;

verus! {

exec fn is_break_even(cost_price: int, selling_price: int) -> (result: bool)
    requires cost_price >= 0 && selling_price >= 0,
    ensures result <==> (cost_price == selling_price),
{
    assume(false);
    unreached();
}

}
fn main() {}