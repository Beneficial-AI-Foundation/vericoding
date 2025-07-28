use vstd::prelude::*;
fn main() {}

verus! {

spec fn is_even(n: u32) -> bool {
    (n % 2) == 0
}

//IMPL is_product_even
fn is_product_even(arr: &Vec<u32>) -> (result: bool)
    ensures
        result <==> (exists|k: int| 0 <= k < arr.len() && is_even(#[trigger] arr[k])),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> !is_even(#[trigger] arr[k]),
        /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
        decreases arr.len() - i,
    {
        /* code modified by LLM (iteration 1): replaced spec function call with executable even check */
        if arr[i] % 2 == 0 {
            /* code modified by LLM (iteration 1): added assertion to connect executable check with spec function */
            assert(is_even(arr[i as int]));
            return true;
        }
        /* code modified by LLM (iteration 1): added assertion to maintain loop invariant */
        assert(!is_even(arr[i as int]));
        i += 1;
    }
    false
}

} // verus!