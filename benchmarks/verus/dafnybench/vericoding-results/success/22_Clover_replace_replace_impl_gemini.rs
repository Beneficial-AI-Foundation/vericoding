// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

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
    let mut i: usize = 0;
    while i < arr.len()
        invariant
            arr.len() == old(arr).len(),
            0 <= i <= arr.len(),
            forall|j: int| 0 <= j < i ==> (old(arr)@[j] > k ==> arr@[j] == -1),
            forall|j: int| 0 <= j < i ==> (old(arr)@[j] <= k ==> arr@[j] == old(arr)@[j]),
            forall|j: int| i <= j < arr.len() ==> arr@[j] == old(arr)@[j]
        decreases arr.len() - i
    {
        if arr[i] > k {
            arr.set(i, -1);
        }
        i = i + 1;
    }
}
// </vc-code>

}
fn main() {}