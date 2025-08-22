use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k]),
    {
        /* code modified by LLM (iteration 1): replaced spec function call with executable even check */
        if arr[i] % 2 == 0 {
            /* code modified by LLM (iteration 1): added proof block to establish postcondition */
            proof {
                assert(is_even(arr[i as int]));
                assert(exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k]));
            }
            return true;
        }
    }
    false
}

} // verus!