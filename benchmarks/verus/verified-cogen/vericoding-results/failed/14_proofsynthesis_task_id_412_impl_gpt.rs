// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec function to filter even elements of a sequence */
spec fn filter_evens(s: Seq<u32>) -> Seq<u32> { s.filter(|x: u32| x % 2 == 0) }
// </vc-helpers>

// <vc-spec>
fn remove_odds(arr: &Vec<u32>) -> (even_list: Vec<u32>)

    ensures
        even_list@ == arr@.filter(|x: u32| x % 2 == 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct even_list from spec sequence using Ghost(...) for ghost argument */
    let even_list = Vec::<u32>::from_seq(Ghost(filter_evens(arr@)));
    even_list
}
// </vc-code>

}
fn main() {}