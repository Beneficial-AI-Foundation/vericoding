// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_negative(x: i32) -> bool { x < 0 }
// </vc-helpers>

// <vc-spec>
fn find_negative_numbers(arr: &Vec<i32>) -> (negative_list: Vec<i32>)

    ensures
        negative_list@ == arr@.filter(|x: i32| x < 0),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using spec fn in invariant to avoid lambda issues */
    let mut negative_list = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant 0 <= index <= arr.len()
        decreases arr.len() - index
        invariant negative_list@ == arr@.subrange(0, index as int).filter(is_negative)
    {
        if arr[index] < 0 {
            negative_list.push(arr[index]);
        }
        index += 1;
    }
    negative_list
}
// </vc-code>

}
fn main() {}