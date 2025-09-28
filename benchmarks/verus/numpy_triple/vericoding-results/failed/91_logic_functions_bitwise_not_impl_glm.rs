// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn numpy_bitwise_not(x: Vec<i8>) -> (result: Vec<i8>)
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == -(x[i] as int + 1)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariant by using while loop with manual increment and added trigger */
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> (#[trigger] result[j]) as int == -(x[j] as int + 1),
    {
        let current = x[i];
        i = i + 1;
        result.push(!current);
    }
    result
// </vc-code>

}
fn main() {}