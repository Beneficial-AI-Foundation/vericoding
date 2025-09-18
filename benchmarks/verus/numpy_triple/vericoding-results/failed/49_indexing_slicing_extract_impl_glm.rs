// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): changed return type to usize for exec compatibility */
fn count_true_exec(condition: Vec<bool>) -> (count: usize)
    ensures count == count_true(condition@) as usize
{
    let mut count: usize = 0;
    for i in 0..condition.len()
        invariant 
            i <= condition.len(),
            count == count_true(condition@.subrange(0, i as int)) as usize,
    {
        if condition[i] {
            count = count + 1;
        }
    }
    count
}
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
/* code modified by LLM (iteration 5): fixed range indexing by using a loop */
{
    let k = count_true_exec(condition);
    let mut result = Vec::new();
    for i in 0..k {
        result.push(arr[i]);
    }
    result
}
// </vc-code>

}
fn main() {}