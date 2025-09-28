use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn replace(arr: &mut Vec<i32>, k: i32)
    ensures 
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] > k ==> arr[i] == -1,
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i],
// </vc-spec>
// <vc-code>
{
    let n = arr.len();
    for i in 0..n
        invariant
            arr.len() == n,
            forall|j: int| 0 <= j < (i as int) ==> 
                (old(arr)[j] > k ==> arr[j] == -1) &&
                (old(arr)[j] <= k ==> arr[j] == old(arr)[j]),
            forall|j: int| (i as int) <= j < (n as int) ==> arr[j] == old(arr)[j],
    {
        if arr[i] > k {
            arr[i] = -1;
        }
    }
}
// </vc-code>

fn main() {}

}