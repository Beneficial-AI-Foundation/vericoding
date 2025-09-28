// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Removed unnecessary helpers and fixed type issues */

// </vc-helpers>

// <vc-spec>
fn logical_not(x: Vec<f64>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x[i] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type conversion and simplified implementation */
    let mut result: Vec<bool> = Vec::new();
    let mut i: nat = 0;
    let len: nat = x.len();
    
    while i < len
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (x@[j] == 0.0),
            i <= len,
    {
        let current = x[i as usize];
        let is_true = current == 0.0;
        result.push(is_true);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}