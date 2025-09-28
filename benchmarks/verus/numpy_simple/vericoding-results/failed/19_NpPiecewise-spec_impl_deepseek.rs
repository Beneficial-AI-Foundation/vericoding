// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed result reference and added proper spec function */
spec fn find_first_match_idx(x: f32, condlist: Seq<spec_fn(f32) -> bool>, start: int) -> (idx: int)
    requires 0 <= start <= condlist.len()
    ensures 
        idx >= -1,
        idx < condlist.len(),
        idx >= 0 ==> condlist[idx](x),
        idx >= 0 ==> forall|j: int| start <= j < idx ==> !condlist[j](x)
{
    if start >= condlist.len() {
        -1
    } else if condlist[start](x) {
        start
    } else {
        find_first_match_idx(x, condlist, start + 1)
    }
}

spec fn apply_first_match(x: f32, condlist: Seq<spec_fn(f32) -> bool>, funclist: Seq<spec_fn(f32) -> f32>) -> (result: f32)
    requires condlist.len() == funclist.len()
    ensures exists|idx: int| 0 <= idx < condlist.len() && condlist[idx](x) ==> result == funclist[idx](x)
{
    let idx = find_first_match_idx(x, condlist, 0);
    if idx >= 0 {
        funclist[idx](x)
    } else {
        0.0f32
    }
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
/* code modified by LLM (iteration 5): Fixed compilation and improved verification */
{
    let mut ret = Vec::new();
    let len = x.len();
    let mut i: usize = 0;
    
    while i < len
        invariant
            ret@.len() == i,
            forall|k: int, j: int| 0 <= k < ret@.len() && 0 <= j < condlist@.len() && condlist@[j](x@[k]) ==> ret@[k] == funclist@[j](x@[k])
        decreases len - i
    {
        let x_val = x[i];
        let mut found = false;
        let mut result_val = 0.0f32;
        let mut j: usize = 0;
        
        while j < condlist.len()
            invariant
                0 <= j <= condlist@.len(),
                !found ==> forall|k: int| 0 <= k < j ==> !condlist@[k](x_val),
                found ==> exists|k: int| 0 <= k < j && condlist@[k](x_val) && result_val == funclist@[k](x_val)
            decreases condlist.len() - j
        {
            if condlist[j](x_val) {
                result_val = funclist[j](x_val);
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            result_val = 0.0f32;
        }
        
        ret.push(result_val);
        i += 1;
    }
    
    ret
}
// </vc-code>


}
fn main() {}