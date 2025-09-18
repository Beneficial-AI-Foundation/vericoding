// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): Removed assumption. The function definition for round_to_nearest_int simply returns the input value as, with `decimals == 0`, no rounding actually occurs. */
spec fn round_to_nearest_int(val: i32) -> i32 {
    val
}
// </vc-helpers>

// <vc-spec>
fn around(a: Vec<i32>, decimals: i32) -> (result: Vec<i32>)
    requires decimals == 0,
    ensures
        result.len() == a.len(),

        forall|i: int| 0 <= i < a.len() && a[i] == 0 ==> result[i] == 0,

        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a.len() && a[i] <= a[j] ==> result[i] <= result[j],

        forall|i: int| 0 <= i < a.len() ==>
            result[i] - 1 <= a[i] && a[i] <= result[i] + 1,

        forall|i: int| 0 <= i < a.len() && a[i] >= 0 ==> result[i] >= 0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Added a `decreases` clause to the loop to ensure termination. */
{
    let mut result: Vec<i32> = Vec::new();
    result.reserve(a.len());

    let mut i = 0;
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k < i ==> round_to_nearest_int(a[k]) == result[k],
            forall|k: int| 0 <= k < i && a[k] == 0 ==> result[k] == 0,
            forall|k: int| 0 <= k < i && a[k] >= 0 ==> result[k] >= 0,
            forall|k: int, l: int| 0 <= k < i && 0 <= l < i && a[k] <= a[l] ==> result[k] <= result[l],
            forall|k: int| 0 <= k < i ==> result[k] - 1 <= a[k] && a[k] <= result[k] + 1,
        decreases a.len() - i
    {
        let rounded_val = a[i];
        result.push(rounded_val);

        proof {
            if i > 0 {
                // The invariant about order preservation needs a more robust `lemma_round_preserves_order`,
                // but given `round_to_nearest_int` is identity for `i32`, the order is trivially preserved.
                // forall|k: int| 0 <= k < i implies round(a[k]) == a[k]
                // so if a[k] <= a[i], then round(a[k]) <= round(a[i]) is just a[k] <= a[i].
                // the invariant already covers this for `k < i` and `l < i`
            }
        }

        i = i + 1;
    }

    result
}
// </vc-code>

}
fn main() {}