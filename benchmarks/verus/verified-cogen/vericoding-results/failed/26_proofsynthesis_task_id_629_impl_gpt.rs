// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec predicate for evenness */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct Vec from filtered sequence using Vec::from_seq, matching ensures predicate */
    let res: Vec<u32> = Vec::from_seq(arr@.filter(|x: u32| x % 2 == 0));
    res
}
// </vc-code>

}
fn main() {}