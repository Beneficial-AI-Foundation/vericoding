// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: &Vec<u32>, x2: &Vec<u32>) -> (result: Vec<u32>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> 
            result[i] == (x1[i] & x2[i]) &&

            (x1[i] & x2[i]) == (x2[i] & x1[i]) &&

            (x1[i] & 0) == 0 &&

            (x1[i] & x1[i]) == x1[i] &&

            result[i] <= x1[i] && result[i] <= x2[i]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed compilation error by using `by(bit_vector)` proof */
    let mut result: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < x1.len()
        invariant
            x1.len() == x2.len(),
            i <= x1.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> 
                result[j] == (x1[j] & x2[j]) &&
                (x1[j] & x2[j]) == (x2[j] & x1[j]) &&
                (x1[j] & 0) == 0 &&
                (x1[j] & x1[j]) == x1[j] &&
                result[j] <= x1[j] && result[j] <= x2[j],
        decreases x1.len() - i
    {
        let val = x1[i] & x2[i];
        proof {
            assert((x1[i] & x2[i]) == (x2[i] & x1[i])) by(bit_vector);
            assert((x1[i] & 0) == 0) by(bit_vector);
            assert((x1[i] & x1[i]) == x1[i]) by(bit_vector);
            assert(val <= x1[i]) by(bit_vector);
            assert(val <= x2[i]) by(bit_vector);
        }
        result.push(val);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}