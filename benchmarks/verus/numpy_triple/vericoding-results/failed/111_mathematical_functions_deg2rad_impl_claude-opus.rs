// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added assertion to prove invariant preservation */
    let mut radians = Vec::new();
    let mut i = 0;
    while i < degrees.len()
        invariant
            0 <= i <= degrees.len(),
            radians.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314 / 18000,
        decreases degrees.len() - i
    {
        let deg_val = degrees[i] as i32;
        let rad_val = deg_val * 314 / 18000;
        let rad = rad_val as i8;
        radians.push(rad);
        
        assert(radians@[i as int] as int == degrees@[i as int] as int * 314 / 18000) by {
            assert(rad as int == rad_val);
            assert(rad_val == deg_val * 314 / 18000);
            assert(deg_val == degrees[i] as i32);
        }
        
        i += 1;
    }
    radians
}
// </vc-code>


}
fn main() {}