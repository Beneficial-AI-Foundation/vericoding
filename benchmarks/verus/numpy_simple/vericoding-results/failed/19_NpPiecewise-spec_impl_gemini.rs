// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn apply_piecewise_one(x_val: f32, condlist: &Vec<spec_fn(f32) -> bool>, funclist: &Vec<spec_fn(f32) -> f32>) -> (ret: f32)
    requires
        condlist.len() == funclist.len(),
    ensures
        forall|j: int| 0 <= j < condlist.len() && condlist@[j](x_val) ==> ret == funclist@[j](x_val),
{
    let mut j = 0;
    while j < condlist.len()
        invariant
            condlist.len() == funclist.len(),
            forall|k: int| 0 <= k < j ==> !condlist@[k](x_val),
        decreases condlist.len() - j
    {
        if condlist[j](x_val) {
            return funclist[j](x_val);
        }
        j = j + 1;
    }
    0.0f32
}
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
    /* code modified by LLM (iteration 2): [fixed compilation error by borrowing condlist and funclist] */
    let mut ret = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            ret.len() == i,
            condlist.len() == funclist.len(),
            forall|k: int, j: int| 0 <= k < i && 0 <= j < condlist@.len() 
                && condlist@[j](x@[k]) ==> ret@[k] == funclist@[j](x@[k]),
        decreases x.len() - i
    {
        let x_i = x[i];
        let y_i = apply_piecewise_one(x_i, &condlist, &funclist);
        ret.push(y_i);
        i = i + 1;
    }
    ret
}
// </vc-code>


}
fn main() {}