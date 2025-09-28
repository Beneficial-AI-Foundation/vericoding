// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn vec_sub_elementwise(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
{
    /* helper modified by LLM (iteration 2): fixed bounds checking and arithmetic overflow */
    let mut result = Vec::with_capacity(c1.len());
    for i in 0..c1.len()
        invariant
            0 <= i <= c1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 0 <= j < c1.len() && 0 <= j < c2.len() && result[j] as int == c1[j] as int - c2[j] as int,
    {
        proof {
            assert(0 <= i < c1.len() && 0 <= i < c2.len());
        }
        let val1 = c1[i] as int;
        let val2 = c2[i] as int;
        proof {
            assert(-128 <= val1 <= 127);
            assert(-128 <= val2 <= 127);
        }
        let diff = val1 - val2;
        proof {
            assert(-255 <= diff <= 255);
        }
        result.push(diff as i8);
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn lagsub(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    requires c1.len() == c2.len(),
    ensures 
        result.len() == c1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == c1[i] as int - c2[i] as int,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): call helper function */
    vec_sub_elementwise(c1, c2)
}
// </vc-code>


}
fn main() {}