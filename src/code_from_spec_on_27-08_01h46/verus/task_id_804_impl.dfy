use vstd::prelude::*;

verus! {

spec fn is_even(n: u32) -> (result: bool) {
    (n % 2) == 0
}
// pure-end

// <vc-helpers>
exec fn is_even_exec(n: u32) -> (result: bool)
    ensures result == is_even(n)
{
    (n % 2) == 0
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
{
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k as int])
    {
        if is_even_exec(arr[i]) {
            return true;
        }
    }
    false
}
// </vc-code>

} // verus!

fn main() {}