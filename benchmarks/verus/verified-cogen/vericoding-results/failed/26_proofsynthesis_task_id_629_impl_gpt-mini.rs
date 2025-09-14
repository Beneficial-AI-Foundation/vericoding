// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): parity predicate */
spec fn is_even(x: u32) -> bool { x % 2 == 0 }
// </vc-helpers>

// <vc-spec>
fn find_even_numbers(arr: &Vec<u32>) -> (even_numbers: Vec<u32>)

    ensures
        even_numbers@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build Vec from filtered seq using from_seq */
    let s: Seq<u32> = arr@.filter(|x: u32| is_even(x));
    let res: Vec<u32> = Vec::from_seq(s);
    res
}
// </vc-code>

}
fn main() {}