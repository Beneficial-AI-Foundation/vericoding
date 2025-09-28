// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn get_value(o: Option<int>) -> int
    recommends o.is_Some()
{
    o.get_Some_0()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): simple min for i8 */
fn min2(a: i8, b: i8) -> i8 {
    if a < b { a } else { b }
}

/* helper modified by LLM (iteration 2): simple max for i8 */
fn max2(a: i8, b: i8) -> i8 {
    if a > b { a } else { b }
}
// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: Vec<i8>) -> (result: (Option<i8>, Option<i8>))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): use while guard with arr.len() and proper invariant to satisfy indexing precondition */
    if arr.len() == 0 {
        return (Option::None, Option::None);
    }
    let mut i: usize = 0;
    let mut min_v: i8 = 0;
    let mut max_v: i8 = 0;
    let mut initialized: bool = false;
    while i < arr.len()
        invariant
            i <= arr.len(),
        decreases arr.len() - i
    {
        let v = arr[i];
        if !initialized {
            min_v = v;
            max_v = v;
            initialized = true;
        } else {
            min_v = min2(min_v, v);
            max_v = max2(max_v, v);
        }
        i += 1;
    }
    if initialized {
        (Option::Some(max_v), Option::Some(min_v))
    } else {
        (Option::None, Option::None)
    }
}
// </vc-code>


}

fn main() {}