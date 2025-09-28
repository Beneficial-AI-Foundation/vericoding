// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simplified conversion without problematic assertions */
fn convert_degree_to_radian(degree: i8) -> (radian: i8)
    ensures
        radian as int == degree as int * 314 / 18000
{
    let numerator = degree as i64 * 314;
    let result = numerator / 18000;
    let radian = result as i8;
    
    proof {
        assert(numerator == degree as int * 314);
        assert(radian as int == result as int);
    }
    
    radian
}
// </vc-helpers>

// <vc-spec>
fn deg2rad(degrees: Vec<i8>) -> (radians: Vec<i8>)
    ensures 
        radians.len() == degrees.len(),
        forall|i: int| 0 <= i < degrees.len() ==> #[trigger] radians@[i] as int == degrees@[i] as int * 314 / 18000
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): main implementation remains the same */
    let mut radians: Vec<i8> = Vec::new();
    let mut i = 0;
    
    while i < degrees.len()
        invariant
            0 <= i <= degrees.len(),
            radians.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314 / 18000,
        decreases degrees.len() - i
    {
        let radian = convert_degree_to_radian(degrees[i]);
        radians.push(radian);
        i += 1;
    }
    
    radians
}
// </vc-code>


}
fn main() {}