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
/* code modified by LLM (iteration 5): Fixed `get_spec` usage on function sequences `condlist` and `funclist` to allow direct function calls like `condlist.get_spec(j)(x.get_spec(i))`. */
{
    let mut ret: Vec<f32> = Vec::new();
    ret.reserve(x.len());

    for i in 0..x.len()
        invariant
            0 <= i <= x.len(),
            ret@.len() == i,
    {
        let mut assigned = false;
        for j in 0..condlist.len()
            invariant
                0 <= j <= condlist.len(),
                assigned == false || exists |k: int| 0 <= k < j && condlist.get_spec(k)(x.get_spec(i)),
            decreases condlist.len() - j
        {
            if condlist.get_spec(j)(x.get_spec(i)) {
                ret.push(funclist.get_spec(j)(x.get_spec(i)));
                assigned = true;
                break;
            }
        }

        if !assigned {
            ret.push(0.0f32);
        }
    }
    ret
}
// </vc-code>


}
fn main() {}