use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn binary_search(arr: &[i32], target: i32) -> (result: Option<usize>)
    // pre-conditions-start
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < arr.len() ==> arr[i] <= arr[j],
    // pre-conditions-end
    // post-conditions-start
    ensures
        match result {
            Some(index) => arr[index as int] == target && arr.len() > 0 && index < arr.len(),
            None => forall|i: int| 0 <= i && i < arr.len() ==> arr[i] != target,
        },
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let n: int = arr.len() as int;
    let mut low: int = 0;
    let mut high: int = n;
    while low < high
        invariant 0 <= low && low <= high && high <= n
        invariant forall |i: int| 0 <= i && i < low ==> arr[i as usize] < target
        invariant forall |i: int| high <= i && i < n ==> arr[i as usize] > target
        decreases (high - low) as nat
    {
        let mid: int = (low + high) / 2;
        let v: i32 = arr[mid as usize];
        if v == target {
            return Some(mid as usize);
        } else if v < target {
            low = mid + 1;
        } else {
            high = mid;
        }
    }
    // loop finished: low == high
    proof {
        assert(low == high);
        assert(forall |i: int| 0 <= i && i < low ==> arr[i as usize] < target);
        assert(forall |i: int| low <= i && i < n ==> arr[i as usize] > target);
        assert(forall |i: int| 0 <= i && i < n ==> arr[i as usize] != target);
    }
    None
    // impl-end
}
// </vc-code>

fn main() {}
}