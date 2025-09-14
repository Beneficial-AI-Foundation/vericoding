// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)

    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,

    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Added decreases clause to fix loop verification */
    let mut res = Vec::new();
    let n = s1.len();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            res@.len() == i * 3,
            forall|j: int| 0 <= j < i ==> res[3 * j] == s1[j],
            forall|j: int| 0 <= j < i ==> res[3 * j + 1] == s2[j],
            forall|j: int| 0 <= j < i ==> res[3 * j + 2] == s3[j],
            n == s1@.len(),
            n == s2@.len(),
            n == s3@.len(),
        decreases n - i
    {
        res.push(s1[i]);
        res.push(s2[i]);
        res.push(s3[i]);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}