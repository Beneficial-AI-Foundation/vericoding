// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed from spec fn to regular fn */
fn is_even(x: u32) -> bool {
    x % 2 == 0
}
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): changed loop condition to use is_even helper */
    let mut even_list: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            even_list@ == arr@.subrange(0, i as int).filter(|x: u32| is_even(x)),
        decreases arr.len() - i,
    {
        if is_even(arr[i]) {
            even_list.push(arr[i]);
        }
        i = i + 1;
    }
    even_list
}
// </vc-code>

}
fn main() {}