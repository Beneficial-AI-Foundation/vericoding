// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_infinite(x: f64) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): avoid redefining is_infinite; provide a trivial helper */
spec fn bool_id(b: bool) -> bool { b }
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
{
    /* code modified by LLM (iteration 5): construct result via Seq mapping using the uninterpreted is_infinite predicate */
    let n = x.len();
    let s: Seq<bool> = Seq::new(n as int, |i: int| is_infinite(x@[i]));
    let result = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}