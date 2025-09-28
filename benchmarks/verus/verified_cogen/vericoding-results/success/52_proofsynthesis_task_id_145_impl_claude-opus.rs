// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn max_spec(a: i32, b: i32) -> i32 {
    if a >= b { a } else { b }
}

spec fn min_spec(a: i32, b: i32) -> i32 {
    if a <= b { a } else { b }
}

proof fn max_difference_exists(arr: &Vec<i32>, max_val: i32, min_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,
        exists|i: int| 0 <= i < arr.len() && arr[i] == max_val,
        exists|i: int| 0 <= i < arr.len() && arr[i] == min_val,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] <= max_val,
        forall|i: int| 0 <= i < arr.len() ==> arr[i] >= min_val,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= max_val - min_val,
{
    assert forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() implies arr[i] - arr[j] <= max_val - min_val by {
        assert(arr[i] <= max_val);
        assert(arr[j] >= min_val);
        assert(arr[i] - arr[j] <= max_val - min_val);
    }
}
// </vc-helpers>

// <vc-spec>
fn max_difference(arr: &Vec<i32>) -> (diff: i32)

    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> i32::MIN / 2 < #[trigger] arr[i] < i32::MAX / 2,

    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= diff,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added decreases clause to fix loop verification error */
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    let mut i: usize = 1;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            exists|j: int| 0 <= j < i && arr[j] == max_val,
            exists|j: int| 0 <= j < i && arr[j] == min_val,
            forall|j: int| 0 <= j < i ==> arr[j] <= max_val,
            forall|j: int| 0 <= j < i ==> arr[j] >= min_val,
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i = i + 1;
    }
    
    proof {
        max_difference_exists(arr, max_val, min_val);
    }
    
    let diff = max_val - min_val;
    diff
}
// </vc-code>

}
fn main() {}