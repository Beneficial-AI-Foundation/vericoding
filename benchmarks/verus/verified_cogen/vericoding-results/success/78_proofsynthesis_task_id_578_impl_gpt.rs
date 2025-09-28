// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn triple_len(n: int) -> int { 3 * n }

proof fn index_agrees(v: &Vec<i32>, i: int)
    requires
        0 <= i < v@.len()
    ensures
        v[i] == v@[i]
{ }
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
    let n = s1.len();
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            s1@.len() == n as int,
            s2@.len() == n as int,
            s3@.len() == n as int,
            res@.len() == 3 * (i as int),
            forall|k: int|
                0 <= k && k < i as int ==> (
                    res@[3 * k] == s1@[k] &&
                    res@[3 * k + 1] == s2@[k] &&
                    res@[3 * k + 2] == s3@[k]
                ),
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