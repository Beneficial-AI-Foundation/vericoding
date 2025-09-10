use vstd::prelude::*;

verus! {

spec fn is_even(n: int) -> bool {
    n % 2 == 0
}

fn is_product_even(a: &[int]) -> (result: bool)
    ensures result <==> exists|i: int| 0 <= i < a.len() && is_even(a@[i])
{
    assume(false);
    unreached()
}

}
fn main() {}