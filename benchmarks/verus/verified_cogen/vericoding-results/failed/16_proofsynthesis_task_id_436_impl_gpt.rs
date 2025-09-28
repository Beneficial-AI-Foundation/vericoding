// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for negativity reused in specs */
spec fn is_neg(x: i32) -> bool { x < 0 }
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): switched to clone + retain for exact filter semantics */
    let mut result = arr.clone();
    result.retain(|x: &i32| *x < 0);
    result
}
// </vc-code>

}
fn main() {}