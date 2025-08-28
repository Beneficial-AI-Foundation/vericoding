use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn abs_diff(a: i32, b: i32) -> int {
    if a >= b { (a - b) as int } else { (b - a) as int }
}

proof fn max_diff_exists(arr: &Vec<i32>)
    requires arr.len() > 0
    ensures exists|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && {
        let diff = arr[i] - arr[j];
        forall|x: int, y: int| 0 <= x < arr.len() && 0 <= y < arr.len() ==> arr[x] - arr[y] <= diff
    }
{
    let mut max_val = arr[0];
    let mut min_val = arr[0];
    
    let mut k: usize = 1;
    while k < arr.len()
        invariant
            1 <= k <= arr.len(),
            exists|idx: int| 0 <= idx < k && arr[idx] == max_val,
            exists|idx: int| 0 <= idx < k && arr[idx] == min_val,
            forall|idx: int| 0 <= idx < k ==> arr[idx] <= max_val,
            forall|idx: int| 0 <= idx < k ==> min_val <= arr[idx],
    {
        if arr[k as int] > max_val {
            max_val = arr[k as int];
        }
        if arr[k as int] < min_val {
            min_val = arr[k as int];
        }
        k += 1;
    }
    
    assert(exists|i: int| 0 <= i < arr.len() && arr[i] == max_val);
    assert(exists|j: int| 0 <= j < arr.len() && arr[j] == min_val);
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
    
    let mut i: usize = 1;
    while i < arr.len()
        invariant
            1 <= i <= arr.len(),
            exists|k: int| 0 <= k < i && arr[k] == max_val,
            exists|k: int| 0 <= k < i && arr[k] == min_val,
            forall|k: int| 0 <= k < i ==> arr[k] <= max_val,
            forall|k: int| 0 <= k < i ==> min_val <= arr[k],
    {
        if arr[i as int] > max_val {
            max_val = arr[i as int];
        }
        if arr[i as int] < min_val {
            min_val = arr[i as int];
        }
        i += 1;
    }
    
    proof {
        assert(forall|k: int| 0 <= k < arr.len() ==> arr[k] <= max_val);
        assert(forall|k: int| 0 <= k < arr.len() ==> min_val <= arr[k]);
        assert(forall|x: int, y: int| 0 <= x < arr.len() && 0 <= y < arr.len() ==> arr[x] - arr[y] <= max_val - min_val);
    }
    
    max_val - min_val
}
// </vc-code>

} // verus!

fn main() {}