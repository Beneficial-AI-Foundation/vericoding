use vstd::prelude::*;

verus! {

// <vc-helpers>
fn is_sorted_prefix(arr: &[i32], p: usize) -> (result: bool)
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l]
{
    let mut i: usize = 0;
    let mut result = true;

    while i <= p
        invariant
            0 <= i <= p + 1,
            result ==> forall|k: int| #![trigger arr[k]] 0 <= k < i ==> forall|l: int| #![trigger arr[l]] p < l < arr.len() ==> arr[k] < arr[l],
        decreases
            p - i
    {
        if i > p {
            break;
        }
        let mut j: usize = p + 1;
        while j < arr.len()
            invariant
                0 <= i <= p,
                p + 1 <= j <= arr.len(),
                result ==> forall|k: int| #![trigger arr[k]] 0 <= k < i ==> forall|l: int| #![trigger arr[l]] p < l < arr.len() ==> arr[k] < arr[l],
                result ==> forall|l: int| #![trigger arr[l]] p < l < j ==> arr[i as int] < arr[l],
            decreases
                arr.len() - j
        {
            if arr[i] >= arr[j] {
                result = false;
                break;
            }
            j = j + 1;
        }
        if !result {
            break;
        }
        i = i + 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn barrier(arr: &[i32], p: usize) -> (result: bool)
    // pre-conditions-start
    requires
        arr.len() > 0,
        0 <= p < arr.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == forall|k: int, l: int| 0 <= k <= p && p < l < arr.len() ==> arr[k] < arr[l],
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    is_sorted_prefix(arr, p)
}
// </vc-code>

fn main() {}
}