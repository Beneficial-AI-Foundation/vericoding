// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed invalid attribute to fix compilation error. */
#[verifier::external_body]
fn is_infinite_exec(x: f64) -> (res: bool)
    ensures res == is_infinite(x),
{
    x.is_infinite()
}
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
/* code modified by LLM (iteration 5): The logic is correct, resubmitting to verify with fixed helper. */
{
    let mut i: usize = 0;
    let mut result = Vec::new();
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == is_infinite(x@[j]),
    {
        let val = x[i];
        let is_inf = is_infinite_exec(val);
        result.push(is_inf);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}