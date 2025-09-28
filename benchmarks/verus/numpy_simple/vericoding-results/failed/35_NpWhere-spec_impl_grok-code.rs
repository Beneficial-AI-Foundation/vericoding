// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
{
    /* helper modified by LLM (iteration 4): correcting the body implementation for where_fn with proper invariants and decreases */
    let length = condition.len();
    let mut index = 0;
    let mut result = Vec::new();
    while index < length
        invariant
            0 <= index <= length,
            result.len() == index,
            forall|k: int| 0 <= k < index ==> result@[k] as int == if condition@[k] { x@[k] as int } else { y@[k] as int },
        decreases length - index
    {
        let elem = if condition[index] { x[index] } else { y[index] };
        result.push(elem);
        index += 1;
    }
    result
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
    /* code modified by LLM (iteration 4): correcting the body implementation for where_with_transform with proper invariants and decreases */
    let length = arr.len();
    let mut index = 0;
    let mut result = Vec::new();
    while index < length
        invariant
            0 <= index <= length,
            result.len() == index,
            forall|k: int| 0 <= k < index ==> result@[k] as int == arr@[k] as int ,
        decreases (length - index) as nat
    {
        result.push(arr[index]);
        index += 1;
    }
    result
}
// </vc-code>


}
fn main() {}