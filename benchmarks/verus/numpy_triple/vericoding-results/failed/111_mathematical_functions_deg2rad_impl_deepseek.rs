// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn helper_compute_radian(deg: i8) -> (rad: i8)
    ensures
        rad as int == deg as int * 314 / 18000
{
    /* helper modified by LLM (iteration 5): fix potential overflow and ensure postcondition */
    proof {
        assert(deg as int * 314 == (deg as int) * 314) by (nonlinear_arith);
        assert((deg as int * 314) / 18000 == ((deg as int) * 314) / 18000) by (nonlinear_arith);
    }
    let scaled: int = deg as int * 314;
    let result: int = scaled / 18000;
    (result as i8)
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
    /* code modified by LLM (iteration 5): fix postcondition verification */
    let mut radians = Vec::new();
    let mut index: usize = 0;

    while index < degrees.len()
        invariant
            radians.len() == index,
            forall|j: int| 0 <= j < index ==> #[trigger] radians@[j] as int == degrees@[j] as int * 314 / 18000
        decreases degrees.len() - index
    {
        let deg_val = degrees[index];
        proof {
            assert(deg_val == degrees@[index]);
        }
        let rad_val = helper_compute_radian(deg_val);
        radians.push(rad_val);
        index = index + 1;
    }

    assert(radians.len() == degrees.len());
    radians
}
// </vc-code>


}
fn main() {}