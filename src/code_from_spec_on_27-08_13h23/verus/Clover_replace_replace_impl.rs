use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed in helpers for this fix
// </vc-helpers>

// <vc-spec>
// <vc-spec>
fn replace(arr: &mut Vec<i32>, k: i32)
    ensures 
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] > k ==> arr[i] == -1,
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i],
// </vc-spec>
// </vc-spec>

// <vc-code>
#[verifier::loop_is_reachable]
fn replace(arr: &mut Vec<i32>, k: i32)
    ensures
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] > k ==> arr[i] == -1,
        forall|i: int| 0 <= i < old(arr).len() ==> old(arr)[i] <= k ==> arr[i] == old(arr)[i],
{
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> old(arr)[j] > k ==> arr[j] == -1,
            forall|j: int| 0 <= j < i ==> old(arr)[j] <= k ==> arr[j] == old(arr)[j],
            forall|j: int| i <= j < arr.len() ==> arr[j] == old(arr)[j],
    {
        if arr[i] > k {
            arr.set(i, -1);
        }
        i = i + 1;
    }
}
// </vc-code>

fn main() {}

}