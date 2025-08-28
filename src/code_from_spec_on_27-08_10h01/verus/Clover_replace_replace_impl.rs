use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn array_unchanged_except_replaced(arr: Seq<i32>, original: Seq<i32>, k: i32, processed: int) -> bool {
    &&& arr.len() == original.len()
    &&& forall|j: int| 0 <= j < processed ==> 
        if original[j] > k { arr[j] == -1 } else { arr[j] == original[j] }
    &&& forall|j: int| processed <= j < arr.len() ==> arr[j] == original[j]
}
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
{
    let ghost original_arr = arr@;
    let mut i = 0;
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            arr.len() == original_arr.len(),
            forall|j: int| 0 <= j < i ==> 
                if original_arr[j] > k { arr@[j] == -1 } else { arr@[j] == original_arr[j] },
            forall|j: int| i <= j < arr.len() ==> arr@[j] == original_arr[j],
        decreases arr.len() - i
    {
        if arr[i] > k {
            arr.set(i, -1);
        }
        i += 1;
    }
}
// </vc-code>

fn main() {}

}