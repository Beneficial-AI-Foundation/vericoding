// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for even numbers */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): filter input sequence and convert to Vec */
    let seq_filtered = arr@.filter(|x: u32| is_even(x));
    seq_filtered.to_vec()
}
// </vc-code>

}
fn main() {}