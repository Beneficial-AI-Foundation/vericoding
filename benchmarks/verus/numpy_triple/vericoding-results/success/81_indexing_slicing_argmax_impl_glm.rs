// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argmax(arr: &Vec<i8>) -> (result: usize)
    requires arr.len() > 0,
    ensures 
        result < arr.len(),
        forall|i: int| 0 <= i && i < arr.len() ==> arr@[i] <= arr@[result as int],
        forall|i: int| 0 <= i && i < result as int ==> arr@[i] < arr@[result as int],
        forall|i: int| (result as int) < i && i < arr.len() ==> arr@[i] <= arr@[result as int],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added result < arr.len() to invariant and extended proof block to cover j=i */
{
    let mut result = 0;
    let mut i = 1;
    while i < arr.len()
        invariant
            0 <= result < i,
            result < arr.len(),
            forall|j: int| 0 <= j < i as int ==> arr@[j] <= arr@[result as int],
            forall|j: int| 0 <= j < result as int ==> arr@[j] < arr@[result as int],
        decreases arr.len() - i,
    {
        if arr[i] > arr[result] {
            proof {
                // We need to prove: forall j in [0, i] (inclusive): arr[j] <= arr[i]
                assert forall|j: int| 0 <= j <= i as int implies arr@[j] <= arr@[i as int] by {
                    if j < i as int {
                        if j < result as int {
                            // j in [0, result): by invariant3, arr[j] < arr[result]
                            assert(arr@[j] < arr@[result as int]);
                            // By the if condition: arr[result] < arr[i]
                            assert(arr@[result as int] < arr@[i as int]);
                            // Therefore, arr[j] < arr[i] -> so arr[j] <= arr[i]
                        } else {
                            // j in [result, i): by invariant2, arr[j] <= arr[result]
                            assert(arr@[j] <= arr@[result as int]);
                            // By the if condition: arr[result] < arr[i]
                            assert(arr@[result as int] < arr@[i as int]);
                            // Therefore, arr[j] <= arr[result] < arr[i] -> so arr[j] < arr[i] -> arr[j] <= arr[i]
                        }
                    } else {
                        // j == i as int
                        assert(arr@[j] == arr@[i as int]);
                    }
                }
            }
            result = i;
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}