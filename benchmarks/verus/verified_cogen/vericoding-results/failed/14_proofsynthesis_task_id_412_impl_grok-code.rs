// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_even(x: u32) -> bool { x % 2u32 == 0 }
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Changed i to nat to fix indexing and type issues, added 2u32 in mod operations */
    let mut result = Vec::new();
    let mut i = 0nat;
    while i < arr@.len()
        invariant
            i <= arr@.len(),
            i >= 0,
            result@ == arr@.subrange(0, i).filter(|x: u32| x % 2u32 == 0),
        decreases arr@.len() - i,
    {
        if arr@[i] % 2u32 == 0 {
            result.push(arr@[i]);
        }
        proof {
            assert(result@ == arr@.subrange(0, i + 1nat).filter(|x: u32| x % 2u32 == 0));
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}