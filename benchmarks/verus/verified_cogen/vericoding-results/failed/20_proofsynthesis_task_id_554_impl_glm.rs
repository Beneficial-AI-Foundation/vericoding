// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): kept spec function for odd number check */
spec fn is_odd_spec(x: u32) -> bool { x % 2 != 0 }
// </vc-helpers>

// <vc-spec>
fn find_odd_numbers(arr: &Vec<u32>) -> (odd_numbers: Vec<u32>)

    ensures
        odd_numbers@ == arr@.filter(|x: u32| x % 2 != 0),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed filter to use closure calling spec function */
{
    let mut result = Vec::new();
    let mut i = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            result@ == arr@.subrange(0, i as int).filter(|x: u32| is_odd_spec(x)),
        decreases arr.len() - i,
    {
        if arr[i] % 2 != 0 {
            result.push(arr[i]);
        }
        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}