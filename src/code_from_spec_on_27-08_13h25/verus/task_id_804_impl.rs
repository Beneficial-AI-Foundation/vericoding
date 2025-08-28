use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// pure-end

// <vc-helpers>
spec fn has_even_element(arr: &Vec<u32>) -> bool {
    exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])
}
// </vc-helpers>

// <vc-spec>
fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    // post-conditions-start
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
    // post-conditions-end
// </vc-spec>

// <vc-code>
fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> !is_even(#[trigger] arr[k as int]),
    {
        let val = arr[i];
        if val % 2 == 0 {
            return true;
        }
        i = i + 1;
    }
    false
}
// </vc-code>

} // verus!

fn main() {}