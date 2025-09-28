// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec map from a sequence of f64 to booleans using is_infinite */
open spec fn map_is_infinite(s: Seq<f64>) -> Seq<bool> {
    Seq::new(s.len(), |i: int| is_infinite(s[i]))
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
{
    /* code modified by LLM (iteration 5): construct result by mapping spec view then converting to Vec */
    let s = map_is_infinite(x@);
    let result = Vec::<bool>::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}