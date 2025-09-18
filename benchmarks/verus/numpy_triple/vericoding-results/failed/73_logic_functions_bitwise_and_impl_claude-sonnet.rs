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
    /* code modified by LLM (iteration 5): Fixed bounds checking with explicit asserts and proper loop index handling */
    let mut result: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < x1.len()
        invariant
            0 <= i <= x1.len(),
            result.len() == i,
            x1.len() == x2.len(),
            forall|j: int| 0 <= j < i ==> 
                result@[j] == (x1@[j] & x2@[j]) &&
                (x1@[j] & x2@[j]) == (x2@[j] & x1@[j]) &&
                (x1@[j] & 0) == 0 &&
                (x1@[j] & x1@[j]) == x1@[j] &&
                result@[j] <= x1@[j] && result@[j] <= x2@[j]
        decreases x1.len() - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let and_result = x1[i] & x2[i];
        result.push(and_result);
        proof {
            assert(result.len() == i + 1);
            assert(i < x1.len());
            assert(i < x2.len());
            assert(result@[i as int] == (x1@[i as int] & x2@[i as int]));
            assert((x1@[i as int] & x2@[i as int]) == (x2@[i as int] & x1@[i as int]));
            assert((x1@[i as int] & 0) == 0);
            assert((x1@[i as int] & x1@[i as int]) == x1@[i as int]);
            assert(result@[i as int] <= x1@[i as int] && result@[i as int] <= x2@[i as int]);
        }
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}