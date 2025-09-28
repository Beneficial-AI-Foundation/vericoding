// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_ediff1d(ary: Vec<i8>) -> (result: Vec<i8>)
    requires ary.len() > 0,
    ensures 
        result.len() == ary.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == ary[i + 1] as int - ary[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): changed loop structure to iterate from 1 to ary.len()-1 */
    let mut result = Vec::with_capacity((ary.len() - 1) as usize);
    let mut i = 1;
    while i < ary.len()
        invariant
            1 <= i <= ary.len(),
            result.len() == i - 1,
            forall|j: int| 0 <= j < i - 1 ==> result[j] as int == ary[j + 1] as int - ary[j] as int,
        decreases ary.len() - i
    {
        result.push(ary[i as usize] - ary[(i - 1) as usize]);
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}