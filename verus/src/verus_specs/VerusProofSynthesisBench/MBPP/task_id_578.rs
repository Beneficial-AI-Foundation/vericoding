use vstd::prelude::*;

verus! {

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
{
    return Vec::new();  // TODO: Remove this line and implement the function body
}

} // verus!

fn main() {}
