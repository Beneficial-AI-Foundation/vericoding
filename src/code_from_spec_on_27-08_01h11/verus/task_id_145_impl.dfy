use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_max_difference_correct(arr: &Vec<i32>, max_val: i32, min_val: i32)
    requires
        arr.len() > 0,
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i] <= max_val,
        forall|i: int| 0 <= i < arr.len() ==> min_val <= #[trigger] arr[i],
        exists|i: int| 0 <= i < arr.len() && arr[i] == max_val,
        exists|i: int| 0 <= i < arr.len() && arr[i] == min_val,
    ensures
        forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() ==> arr[i] - arr[j] <= max_val - min_val,
{
    assert forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() implies arr[i] - arr[j] <= max_val - min_val by {
        assert(arr[i] <= max_val);
        assert(min_val <= arr[j]);
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
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut i = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            forall|k: int| 0 <= k < i ==> arr[k] <= max_val,
            forall|k: int| 0 <= k < i ==> min_val <= arr[k],
            exists|k: int| 0 <= k < i && arr[k] == max_val,
            exists|k: int| 0 <= k < i && arr[k] == min_val,
        decreases arr.len() - i
    {
        if arr[i] > max_val {
            max_val = arr[i];
        }
        if arr[i] < min_val {
            min_val = arr[i];
        }
        i += 1;
    }
    
    proof {
        lemma_max_difference_correct(arr, max_val, min_val);
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}