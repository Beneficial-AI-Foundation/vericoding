use vstd::prelude::*;

fn main() {}

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
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < s1.len()
        invariant
            idx <= s1.len(),
            s1@.len() == s2@.len() && s2@.len() == s3@.len(),
            result@.len() == idx * 3,
            forall|i: int| 0 <= i < idx ==> (
                result[3 * i] == s1[i] && 
                result[3 * i + 1] == s2[i] && 
                result[3 * i + 2] == s3[i]
            ),
        decreases s1.len() - idx
    {
        result.push(s1[idx]);
        result.push(s2[idx]);
        result.push(s3[idx]);
        idx += 1;
    }
    
    result
}

} // verus!