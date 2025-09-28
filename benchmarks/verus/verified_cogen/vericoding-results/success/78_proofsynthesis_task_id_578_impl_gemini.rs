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
    let mut res = Vec::new();
    let mut i: usize = 0;
    let len = s1.len();

    while i < len
        invariant
            i <= len,
            s1@.len() == len,
            s2@.len() == len,
            s3@.len() == len,
            res@.len() == 3 * (i as int),
            forall|j: int| 0 <= j < i ==> (
                res@[3 * j] == s1@[j] &&
                res@[3 * j + 1] == s2@[j] &&
                res@[3 * j + 2] == s3@[j]
            ),
        decreases len - i
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