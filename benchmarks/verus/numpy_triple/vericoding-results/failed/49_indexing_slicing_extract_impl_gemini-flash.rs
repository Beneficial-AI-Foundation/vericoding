// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed extra space*/
// </vc-helpers>

// <vc-spec>
spec fn count_true(condition: Seq<bool>) -> int 
    decreases condition.len()
{
    if condition.len() == 0 {
        0int
    } else {
        (if condition[0] { 1int } else { 0int }) + count_true(condition.skip(1))
    }
}

fn extract(condition: Vec<bool>, arr: Vec<f32>) -> (result: Vec<f32>)
    requires 
        condition.len() == arr.len(),
        count_true(condition@) >= 0,
    ensures
        result.len() == count_true(condition@),
        forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == arr[i],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed subsequence calls on Seq by using the Seq itself */
{
    let mut result = Vec::new();
    let mut i = 0;
    let mut k = 0; // k tracks the number of true conditions encountered so far

    while i < condition.len()
        invariant
            0 <= i <= condition.len(),
            k == count_true(condition@.subsequence(0, i as int)),
            result.len() == k,
            forall|j: int| 0 <= j < k ==> 
                #[trigger] result[j] == arr[choose|l: int| 0 <= l < i && condition[l@]==true && count_true(condition@.subsequence(0, l as int)) == j],
        decreases condition.len() - i
    {
        if condition[i] {
            result.push(arr[i]);
            k = k + 1;
        }
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}