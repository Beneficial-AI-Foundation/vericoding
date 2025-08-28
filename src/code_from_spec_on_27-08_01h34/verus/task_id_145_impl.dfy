use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: i32, b: i32) -> i32 {
    if a >= b { (a - b) as i32 } else { (b - a) as i32 }
}

spec fn max_diff_in_range(arr: &Vec<i32>, start: int, end: int) -> i32
    decreases end - start
{
    if start >= end {
        0
    } else if start + 1 == end {
        0
    } else {
        let mid_diff = abs_diff(arr[start], arr[start + 1]);
        let rest_diff = max_diff_in_range(arr, start + 1, end);
        if mid_diff >= rest_diff { mid_diff } else { rest_diff }
    }
}
// </vc-helpers>

// <vc-spec>
fn max_difference(arr: &Vec<i32>) -> (diff: i32)
    // pre-conditions-start
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut max_diff = 0i32;
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|x: int, y: int| 0 <= x < i && 0 <= y < arr.len() ==> arr[x] - arr[y] <= max_diff,
            forall|x: int, y: int| 0 <= x < arr.len() && 0 <= y < i ==> arr[x] - arr[y] <= max_diff,
        decreases arr.len() - i
    {
        let mut j = 0;
        while j < arr.len()
            invariant
                0 <= i < arr.len(),
                0 <= j <= arr.len(),
                forall|x: int, y: int| 0 <= x < i && 0 <= y < arr.len() ==> arr[x] - arr[y] <= max_diff,
                forall|x: int, y: int| 0 <= x < arr.len() && 0 <= y < i ==> arr[x] - arr[y] <= max_diff,
                forall|y: int| 0 <= y < j ==> arr[i] - arr[y] <= max_diff,
            decreases arr.len() - j
        {
            let diff = arr[i] - arr[j];
            if diff > max_diff {
                max_diff = diff;
            }
            j += 1;
        }
        i += 1;
    }
    
    max_diff
}
// </vc-code>

} // verus!

fn main() {}