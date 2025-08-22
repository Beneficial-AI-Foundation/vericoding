use vstd::prelude::*;

fn main() {
    let v1 = vec![1, 3, 5];
    let v2 = vec![2, 4, 6];
    let v3 = vec![7, 8, 9];
    let result = interleave(&v1, &v2, &v3);
    println!("Interleaved: {:?}", result);
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
    let len = s1.len();
    
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause */
    while j < len
        invariant
            j <= len,
            result@.len() == j * 3,
            forall|i: int| 0 <= i < j ==> (
                result[3 * i] == s1[i] && 
                result[3 * i + 1] == s2[i] && 
                result[3 * i + 2] == s3[i]
            ),
        decreases len - j
    {
        result.push(s1[j]);
        result.push(s2[j]);
        result.push(s3[j]);
        j += 1;
    }
    
    result
}

} // verus!