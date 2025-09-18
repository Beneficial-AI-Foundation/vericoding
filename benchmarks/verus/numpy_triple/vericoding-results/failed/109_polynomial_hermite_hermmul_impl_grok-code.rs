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
    /* code modified by LLM (iteration 5): changed length variables to usize to fix compilation errors with int type in executable code */
    if c1.len() == 0 || c2.len() == 0 {
        let mut v: Vec<i32> = Vec::new();
        v.push(0);
        v
    } else {
        let c1_len: usize = c1.len();
        let c2_len: usize = c2.len();
        let result_len: usize = c1_len + c2_len - 1;
        let mut result: Vec<i32> = Vec::new();
        for _ in 0..result_len {
            result.push(0);
        }
        for i in 0..c1_len {
            for j in 0..c2_len {
                let idx: usize = i + j;
                proof {
                    assert(idx < result_len);
                    assert((idx as int) < (result_len as int));
                    assert(idx >= 0);
                }
                let new_val = (result[idx] as i64 + (c1[i] as i64) * (c2[j] as i64)) as i32;
                result[idx] = new_val;
            }
        }
        result
    }
}
// </vc-code>

}
fn main() {}