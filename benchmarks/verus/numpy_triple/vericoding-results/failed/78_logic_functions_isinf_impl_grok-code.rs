// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): adding body to spec fn is_infinite */ spec fn is_infinite(x: f64) -> bool { x.is_infinite() }
// </vc-helpers>

// <vc-spec>
fn isinf(x: Vec<f64>) -> (result: Vec<bool>)
    requires x.len() < usize::MAX,
    ensures 
        result.len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> {
            result[i] == is_infinite(x[i])
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): implementing vectorized isinf with loop */ {
    let mut result: Vec<bool> = Vec::with_capacity(x.len());
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
    {
        result.push(is_infinite(x[i]));
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}