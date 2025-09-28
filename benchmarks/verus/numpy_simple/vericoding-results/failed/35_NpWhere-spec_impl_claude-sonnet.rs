// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function for where_fn implementation */
fn select_value(condition: bool, x_val: i8, y_val: i8) -> (result: i8)
    ensures result as int == if condition { x_val as int } else { y_val as int }
{
    if condition { x_val } else { y_val }
}
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
    /* code modified by LLM (iteration 5): implement where_with_transform function body */
    let mut result = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            result.len() == i,
            i <= arr.len(),
    {
        result.push(arr[i]);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}