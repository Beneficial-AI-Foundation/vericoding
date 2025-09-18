// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
{
    /* code modified by LLM (iteration 5): fixed while loop syntax by placing invariant inside the loop body */
    let mut num_true = 0;
    let mut i = 0;
    while i < condition.len() {
        invariant i <= condition.len();
        invariant num_true <= i;
        invariant num_true == count_true(condition@.take(i as int));
        decreases condition.len() - i;
        if condition[i] {
            num_true = num_true + 1;
        }
        i = i + 1;
    }
    let mut result = Vec::new();
    i = 0;
    while i < num_true {
        invariant i <= num_true;
        invariant result.len() == i;
        invariant forall |k: int| 0 <= k < i ==> #[trigger] result@[k] == arr@[k];
        decreases num_true - i;
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}