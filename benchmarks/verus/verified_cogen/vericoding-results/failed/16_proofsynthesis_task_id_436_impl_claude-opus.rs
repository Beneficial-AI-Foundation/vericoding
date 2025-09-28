// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed move error by not moving negative_list in loop */
    let mut negative_list = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            negative_list@ == arr@.take(i as int).filter(|x: i32| x < 0),
        decreases arr.len() - i,
    {
        if arr[i] < 0 {
            negative_list.push(arr[i]);
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                assert(arr@[i as int] < 0);
                assert(negative_list@ == arr@.take((i + 1) as int).filter(|x: i32| x < 0));
            }
        } else {
            proof {
                assert(arr@.take((i + 1) as int) == arr@.take(i as int).push(arr@[i as int]));
                assert(arr@[i as int] >= 0);
                assert(negative_list@ == arr@.take((i + 1) as int).filter(|x: i32| x < 0));
            }
        }
        i += 1;
    }
    assert(arr@.take(arr.len() as int) == arr@);
    negative_list
}
// </vc-code>

}
fn main() {}