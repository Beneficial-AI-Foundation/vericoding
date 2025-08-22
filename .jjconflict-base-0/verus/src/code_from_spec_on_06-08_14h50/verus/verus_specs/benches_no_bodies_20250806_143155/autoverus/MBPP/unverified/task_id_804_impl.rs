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
    /* code modified by LLM (iteration 1): Fixed mode error by using exec function and added proper proof structure */
    for i in 0..arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> !is_even(arr[k]),
    {
        if arr[i] % 2 == 0 {
            proof {
                assert(is_even(arr[i as int]));
                assert(exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k]));
            }
            return true;
        }
    }
    
    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> !is_even(arr[k]));
        assert(!(exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])));
    }
    false
}

} // verus!