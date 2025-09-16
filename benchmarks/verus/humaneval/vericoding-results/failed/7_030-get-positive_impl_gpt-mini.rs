// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): predicate for positive ints */
spec fn is_positive(x: int) -> bool { x > 0 }
// </vc-helpers>

// <vc-spec>
fn get_positive(input: Vec<i32>) -> (positive_list: Vec<i32>)

    ensures
        positive_list@ == input@.filter(|x: i32| x > 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate using int indices and collect positives with correct seq slicing */
    let mut res: Vec<i32> = Vec::new();
    let mut i: int = 0;
    let len: int = input@.len();
    while i < len
        invariant
            res@ == input@[0..i].filter(|x: i32| x > 0),
            i >= 0,
            i <= len,
        decreases len - i
    {
        let v: i32 = input[i as usize];
        if v > 0 {
            res.push(v);
        }
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}