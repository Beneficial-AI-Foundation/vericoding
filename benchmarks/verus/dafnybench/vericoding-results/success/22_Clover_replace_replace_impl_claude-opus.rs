use vstd::prelude::*;

verus! {

// <vc-helpers>
// No additional helpers needed for this implementation
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
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            arr.len() == n,
            forall|j: int| 0 <= j < i ==> old(arr)[j] > k ==> arr[j] == -1,
            forall|j: int| 0 <= j < i ==> old(arr)[j] <= k ==> arr[j] == old(arr)[j],
            forall|j: int| i <= j < n ==> arr[j] == old(arr)[j],
        decreases n - i,
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