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
    let ghost original_arr = arr@;
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            arr.len() == original_arr.len(),
            forall|j: int| 0 <= j < i ==> #[trigger] original_arr[j] > k ==> #[trigger] arr@[j] == -1,
            forall|j: int| 0 <= j < i ==> #[trigger] original_arr[j] <= k ==> #[trigger] arr@[j] == original_arr[j],
            forall|j: int| i <= j < arr.len() ==> #[trigger] arr@[j] == #[trigger] original_arr[j],
        decreases arr.len() - i
    {
        if arr[i] > k {
            arr.set(i, -1);
        }
        i += 1;
    }
    assert(forall|j: int| 0 <= j < original_arr.len() ==> original_arr[j] > k ==> arr@[j] == -1);
    assert(forall|j: int| 0 <= j < original_arr.len() ==> original_arr[j] <= k ==> arr@[j] == original_arr[j]);
}
// </vc-code>

fn main() {}

}