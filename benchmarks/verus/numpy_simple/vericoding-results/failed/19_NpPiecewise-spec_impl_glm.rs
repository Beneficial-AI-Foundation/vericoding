// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn piecewise(x: Vec<f32>, condlist: Vec<spec_fn(f32) -> bool>, funclist: Vec<spec_fn(f32) -> f32>) -> (ret: Vec<f32>)
    requires condlist@.len() == funclist@.len(),
    ensures
        ret@.len() == x@.len(),
        forall|i: int, j: int| 0 <= i < x@.len() && 0 <= j < condlist@.len() && 
            condlist@[j](x@[i]) ==> ret@[i] == funclist@[j](x@[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using Vec::from_seq */
    let mut ret = Seq::empty();
    let n = x.len();
    let m = condlist.len();
    for i in 0..n {
        let mut value = 0.0f32;
        for j in 0..m {
            if condlist[j](x[i]) {
                value = funclist[j](x[i]);
                break;
            }
        }
        ret = ret.push(value);
    }
    Vec::from_seq(ret)
}
// </vc-code>


}
fn main() {}