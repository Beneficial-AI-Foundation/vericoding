// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): moved int casting to ghost code */
fn deg2rad_helper(deg: i8) -> (rad: i8)
    ensures
        rad as int == deg as int * 314 / 18000
{
    proof {
        let deg_int = deg as int;
        let rad_int = deg_int * 314 / 18000;
        assert(rad_int as i8 as int == rad_int);
    }
    (deg as int * 314 / 18000) as i8
}
// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): removed int casting from executable code */
{
    let mut radians = Vec::new();
    let len = degrees.len();
    
    for i in 0..len
        invariant
            radians.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314 / 18000
    {
        let rad = deg2rad_helper(degrees[i]);
        radians.push(rad);
    }
    
    radians
}
// </vc-code>


}
fn main() {}