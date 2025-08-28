use vstd::prelude::*;

verus! {

// <vc-helpers>
// No updates needed for helpers
// </vc-helpers>

// <vc-spec>
fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)
    // pre-conditions-start
    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,
    // pre-conditions-end
    // post-conditions-start
    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
    // post-conditions-end
// </vc-spec>

// <vc-code>
{
    let mut res: Vec<i32> = Vec::new();
    let len = s1.len();
    let mut i: usize = 0;

    while i < len
        invariant
            i <= len,
            res@.len() == i * 3,
            forall|k: int| 0 <= k < i ==> (res@[3 * k] == s1@[k] && res@[3 * k + 1] == s2@[k] && res@[3 * k + 2] == s3@[k]),
        decreases len - i
    {
        assert(i < s1@.len());
        assert(i < s2@.len());
        assert(i < s3@.len());
        res.push(s1[i]);
        res.push(s2[i]);
        res.push(s3[i]);
        i = i + 1;
    }

    res
}
// </vc-code>

} // verus!

fn main() {}