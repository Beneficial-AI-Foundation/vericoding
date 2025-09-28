// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial length non-negativity lemma */
fn lemma_len_nonneg(v: Vec<i8>)
{
    proof {
        assert(v.len() >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn polyadd(c1: Vec<i8>, c2: Vec<i8>) -> (result: Vec<i8>)
    ensures
        result.len() == if c1.len() >= c2.len() { c1.len() } else { c2.len() },
        forall|i: int| 0 <= i < result.len() ==> {
            if i < c1.len() && i < c2.len() {
                result[i] as int == c1[i] as int + c2[i] as int
            } else if i < c1.len() && i >= c2.len() {
                result[i] as int == c1[i] as int
            } else if i >= c1.len() && i < c2.len() {
                result[i] as int == c2[i] as int
            } else {
                result[i] as int == 0
            }
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implement element-wise addition with proper truncate cast parentheses */
    let mut res: Vec<i8> = Vec::new();
    let len1 = c1.len();
    let len2 = c2.len();
    let max_len = if len1 >= len2 { len1 } else { len2 };
    let mut i: usize = 0;
    while i < max_len
        invariant
            res.len() == i,
            i <= max_len,
        decreases max_len - i
    {
        let a: i32 = if i < c1.len() { c1[i] as i32 } else { 0 };
        let b: i32 = if i < c2.len() { c2[i] as i32 } else { 0 };
        let sum_i32 = a + b;
        let sum: i8 = #[verifier::truncate] (sum_i32 as i8);
        res.push(sum);
        i = i + 1;
    }
    res
}
// </vc-code>


}
fn main() {}