use vstd::prelude::*;

fn main() {
}

verus! {

fn interleave(s1: &Vec<i32>, s2: &Vec<i32>, s3: &Vec<i32>) -> (res: Vec<i32>)
    requires
        s1@.len() == s2@.len() && s2@.len() == s3@.len(),
        0 <= (s1@.len() * 3) <= i32::MAX,
    ensures
        res@.len() == s1@.len() * 3,
        forall|i: int|
            0 <= i < s1@.len() ==> (res[3 * i] == s1[i] && res[3 * i + 1] == s2[i] && res[3 * i + 2]
                == s3[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < s1.len()
        invariant
            s1@.len() == s2@.len() && s2@.len() == s3@.len(),
            0 <= i <= s1@.len(),
            result@.len() == i * 3,
            forall|j: int| 0 <= j < i ==> (
                result@[3 * j] == s1@[j] && 
                result@[3 * j + 1] == s2@[j] && 
                result@[3 * j + 2] == s3@[j]
            ),
    {
        result.push(s1[i]);
        result.push(s2[i]);
        result.push(s3[i]);
        i += 1;
    }
    
    result
}

} // verus!