use vstd::prelude::*;

verus! {

#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
{
    let mut i = 0;
    while i <= p
        invariant
            0 <= i <= p + 1,
            forall|k: int, l: int| 0 <= k < i && p < l < arr.len() ==> arr[k] < arr[l],
    {
        let mut j = p + 1;
        while j < arr.len()
            invariant
                p + 1 <= j <= arr.len(),
                forall|l: int| p < l < j ==> arr[i] < arr[l],
            {
                if arr[i] >= arr[j] {
                    return false;
                }
                j += 1;
            }
        i += 1;
    }
    true
}

fn main() {}
}