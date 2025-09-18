// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): is_zero_vec predicate */
spec fn is_zero_vec(v: Vec<i32>) -> bool { forall|i: int| 0 <= i < v.len() ==> v[i] == 0 }

/* helper modified by LLM (iteration 5): trivial tautology helper */
proof fn helper_always_true() ensures true { }
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
    /* code modified by LLM (iteration 5): implement polynomial convolution using usize indices and loops */
    let n: usize = c1.len();
    let m: usize = c2.len();
    if n == 0 || m == 0 {
        let mut res: Vec<i32> = Vec::new();
        res.push(0);
        res
    } else {
        let res_len: usize = n + m - 1;
        let mut res: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < res_len
            decreases res_len - k
        {
            res.push(0);
            k += 1;
        }
        let mut i: usize = 0;
        while i < n
            decreases n - i
        {
            let mut j: usize = 0;
            while j < m
                decreases m - j
            {
                let idx: usize = i + j;
                let sum = res[idx] + c1[i] * c2[j];
                res.set(idx, sum);
                j += 1;
            }
            i += 1;
        }
        res
    }
}
// </vc-code>

}
fn main() {}