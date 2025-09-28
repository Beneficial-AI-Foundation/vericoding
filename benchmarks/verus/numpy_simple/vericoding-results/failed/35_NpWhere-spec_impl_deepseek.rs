// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Removed helper functions to use inline logic */

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
    /* code modified by LLM (iteration 5): Replaced helper calls with inline conditionals */
    let mut result = Vec::new();
    let n = condition.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == (if condition@[j] { x@[j] as int } else { y@[j] as int })
        decreases n - i
    {
        let c = condition.index(i);
        let x_val = x.index(i);
        let y_val = y.index(i);
        let elem = if c { x_val } else { y_val };
        result.push(elem);
        i += 1;
    }
    
    result
}

{
    let mut result = Vec::new();
    let n = arr.len();
    let mut i = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            result.len() == i
        decreases n - i
    {
        let val = arr.index(i);
        let transformed = if val > 0 { val } else { -val };
        result.push(transformed);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}