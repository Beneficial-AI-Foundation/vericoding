// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Make helper function exec mode instead of proof */
fn numpy_negative_helper(val: i8) -> (result: i8)
    ensures
        result as int == -(val as int)
{
    let neg: i8 = -(val as int) as i8;
    neg
}
// </vc-helpers>

// <vc-spec>
fn numpy_negative(x: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> result[i] as int == -(x[i] as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Use exec mode helper function and add proper variable declarations */
{
    let mut result: Vec<i8> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j] as int == -(x@[j] as int)
        decreases x.len() - i
    {
        let val = x[i];
        let neg_val = numpy_negative_helper(val);
        result.push(neg_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}