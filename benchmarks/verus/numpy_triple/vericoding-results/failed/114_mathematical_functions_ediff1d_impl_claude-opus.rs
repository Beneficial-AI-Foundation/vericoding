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
    /* code modified by LLM (iteration 3): Added decreases clause to while loop */
    let mut result = Vec::new();
    let mut i = 0;
    while i < ary.len() - 1
        invariant
            0 <= i <= ary.len() - 1,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] as int == ary[j + 1] as int - ary[j] as int,
        decreases ary.len() - 1 - i
    {
        let diff = ary[i + 1] - ary[i];
        result.push(diff);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}