use vstd::prelude::*;

verus! {

// <vc-helpers>

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
    let n = arr.len();
    let mut result = true;
    for k in 0..=p {
        invariant(
            (k <= p) &&
            result &&
            (forall |k': usize| 
                (0 <= k' && k' < k) &&
                (forall |l: usize| 
                    #[trigger]
                    (p < l && l < n) 
                    ==> arr[k'] < arr[l])
            )
        );
        let mut l = p+1;
        while l < n {
            invariant(
                (l >= p+1) &&
                (forall |l': usize| 
                    #[trigger]
                    (p+1 <= l' && l' < l) 
                    ==> arr[k] < arr[l'])
            );
            if arr[k] >= arr[l] {
                result = false;
                break;
            } else {
                l += 1;
            }
        }
        if !result {
            break;
        }
    }
    return result;
}
// </vc-code>

fn main() {}
}