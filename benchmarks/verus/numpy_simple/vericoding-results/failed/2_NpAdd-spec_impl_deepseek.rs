// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed overflow handling with proper saturation logic */
fn add_helper(a_val: i8, b_val: i8) -> (result: i8)
    ensures result as int == a_val as int + b_val as int
{
    let sum_int = a_val as int + b_val as int;
    if sum_int > 127 {
        127i8
    } else if sum_int < -128 {
        -128i8
    } else {
        sum_int as i8
    }
}
// </vc-helpers>

// <vc-spec>
fn add(a: Vec<i8>, b: Vec<i8>) -> (result: Vec<i8>)
    requires a.len() == b.len(),
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == a[i] as int + b[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let mut result = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] as int == a@[j] as int + b@[j] as int,
            i <= a.len()
        decreases a.len() - i
    {
        let a_val = a[i];
        let b_val = b[i];
        let sum = add_helper(a_val, b_val);
        result.push(sum);
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}