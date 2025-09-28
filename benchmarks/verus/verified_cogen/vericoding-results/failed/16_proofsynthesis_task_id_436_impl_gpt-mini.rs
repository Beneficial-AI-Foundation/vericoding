// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate to check negativity */
spec fn is_negative(x: i32) -> bool { x < 0 }
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate and collect negatives, maintain invariant using Seq::slice */
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            res@ == arr@.slice(0, i as nat).filter(|x: i32| x < 0),
            (i as nat) <= arr@.len(),
        decreases arr@.len() - (i as nat)
    {
        let x: i32 = *arr.get(i).unwrap();
        if x < 0 {
            res.push(x);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}