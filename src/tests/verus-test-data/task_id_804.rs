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
    // impl-start
    let mut index = 0;
    while index < arr.len()
        // invariants-start
        invariant
            0 <= index <= arr.len(),
            forall|k: int| 0 <= k < index ==> !(is_even(#[trigger] arr[k])),
        // invariants-end
    {
        if (arr[index] % 2 == 0) {
            return true;
        }
        index += 1;
    }
    false
    // impl-end
}

} // verus!

fn main() {}
