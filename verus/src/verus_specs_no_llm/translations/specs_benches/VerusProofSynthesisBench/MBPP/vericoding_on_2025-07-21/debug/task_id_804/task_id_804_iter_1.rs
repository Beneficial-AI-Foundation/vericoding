use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// pure-end

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
    // post-conditions-end
{
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k]),
    {
        if is_even(arr[i]) {
            return true;
        }
    }
    false
}

} // verus!

fn main() {}