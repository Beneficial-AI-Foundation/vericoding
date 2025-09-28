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
    let mut ret = Vec::new();
    for i in 0..x.len() {
        let val = x[i];
        let mut temp = val;
        for j in 0..condlist.len() {
            if condlist[j](val) {
               temp = funclist[j](val);
               break;
            }
        }
        ret.push(temp);
    }
    ret
}
// </vc-code>


}
fn main() {}