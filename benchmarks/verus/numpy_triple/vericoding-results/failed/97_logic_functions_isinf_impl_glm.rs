// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x@[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): replaced uninterpreted function call with built-in method */ {
    let mut result = Vec::with_capacity(x.len());
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == x@[j].is_infinite(),
        decreases x.len() - i
    {
        result.push(x@[i].is_infinite());
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}