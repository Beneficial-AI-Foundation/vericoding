// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added helper function to find the index of first matching condition with ghost casting */
fn find_matching_index(val: f32, condlist: &Vec<spec_fn(f32) -> bool>) -> (ret: usize)
    requires condlist@.len() > 0,
    ensures ret < condlist@.len(),
{
    let mut j = 0;
    while j < condlist.len()
        invariant j <= condlist@.len(),
        decreases condlist@.len() - j
    {
        proof {
            let ghost_j = j as int;
            if condlist@[ghost_j](val) {
                return j;
            }
        }
        j += 1;
    }
    0
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
    /* code modified by LLM (iteration 5): properly compute result values by finding matching conditions and applying corresponding functions with ghost casting */
    let mut result = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            result@.len() == i,
            forall|k: int, j: int| 0 <= k < i && 0 <= j < condlist@.len() &&
                condlist@[j](x@[k]) ==> result@[k] == funclist@[j](x@[k]),
        decreases x.len() - i
    {
        let value = x[i];
        let j = find_matching_index(value, &condlist);
        proof {
            let ghost_j = j as int;
            let computed_value = funclist@[ghost_j](value);
            result.push(computed_value);
        }
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}