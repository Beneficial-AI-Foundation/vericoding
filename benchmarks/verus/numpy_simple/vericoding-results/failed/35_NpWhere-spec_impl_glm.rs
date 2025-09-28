// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn where_fn(condition: Vec<bool>, x: Vec<i8>, y: Vec<i8>) -> (result: Vec<i8>)
    requires 
        condition.len() == x.len(),
        x.len() == y.len(),
    ensures 
        result.len() == condition.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] as int == if condition[i] { x[i] as int } else { y[i] as int }
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}

fn where_with_transform(arr: Vec<i8>) -> (result: Vec<i8>)
    requires arr.len() >= 0,
    ensures 
        result.len() == arr.len()
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): implemented where_fn with loop and invariants */
    let mut result = Vec::new();
    let n = condition.len();
    for i in 0..n
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == if condition[j] { x[j] as int } else { y[j] as int }
    {
        if condition[i] {
            result.push(x[i]);
        } else {
            result.push(y[i]);
        }
    }
    result
}
// </vc-code>


}
fn main() {}