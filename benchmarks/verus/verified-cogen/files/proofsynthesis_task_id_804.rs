use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)

    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    assume(false);
    unreached();
}

}
fn main() {}