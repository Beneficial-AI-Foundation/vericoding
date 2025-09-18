// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] == c1[i] * c2[0],
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] == c2[i] * c1[0],

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Added decreases clause to fix loop verification */
    if c1.len() == 0 || c2.len() == 0 {
        let mut result = Vec::new();
        result.push(0);
        proof {
            assert(result.len() == 1);
            assert(result[0] == 0);
        }
        result
    } else {
        let result_len = c1.len() + c2.len() - 1;
        let mut result: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < result_len
            invariant
                i <= result_len,
                result.len() == i,
            decreases result_len - i
        {
            let mut sum = 0i32;
            let mut j: usize = 0;
            while j <= i
                invariant
                    j <= i + 1,
                decreases i + 1 - j
            {
                if j < c1.len() && i >= j && i - j < c2.len() {
                    sum = sum + c1[j] * c2[i - j];
                }
                j = j + 1;
            }
            result.push(sum);
            i = i + 1;
        }
        proof {
            assert(result.len() == c1.len() + c2.len() - 1);
            if c2.len() == 1 && c1.len() > 0 {
                assert forall|i: int| 0 <= i < c1.len() implies result[i] == c1[i] * c2[0] by {
                    assert(result[i] == c1[i] * c2[0]);
                }
            }
            if c1.len() == 1 && c2.len() > 0 {
                assert forall|i: int| 0 <= i < c2.len() implies result[i] == c2[i] * c1[0] by {
                    assert(result[i] == c1[0] * c2[i]);
                }
            }
        }
        result
    }
}
// </vc-code>

}
fn main() {}