// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed redundant helper, which was flagged as a verification bypass */
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
/* code modified by LLM (iteration 5): rely on environment's spec for f64::is_infinite and assert the connection */
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_infinite(x@[j]),
        decreases x.len() - i,
    {
        let is_inf = x[i].is_infinite();
        proof {
            assert(is_inf == is_infinite(x[i]));
        }
        result.push(is_inf);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}