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

// </vc-helpers>

// <vc-spec>
fn largest_smallest_integers(arr: Vec<i8>) -> (result: (Option<i8>, Option<i8>))
// </vc-spec>
// <vc-code>
{
    if arr.len() == 0 {
        (Option::None, Option::None)
    } else {
        let mut min_val = arr[0];
        let mut max_val = arr[0];
        let mut i = 1;
        while i < arr.len()
            invariant
                1 <= i <= arr.len(),
                forall |j: int| 0 <= j < i ==> min_val <= arr@[j],
                forall |j: int| 0 <= j < i ==> max_val >= arr@[j],
                exists |j: int| 0 <= j < i && min_val == arr@[j],
                exists |j: int| 0 <= j < i && max_val == arr@[j],
            decreases arr.len() - i
        {
            if arr[i] < min_val {
                min_val = arr[i];
            }
            if arr[i] > max_val {
                max_val = arr[i];
            }
            i += 1;
        }
        (Option::Some(min_val), Option::Some(max_val))
    }
}
// </vc-code>


}

fn main() {}