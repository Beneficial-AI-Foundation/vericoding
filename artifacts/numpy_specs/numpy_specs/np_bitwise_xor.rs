use vstd::prelude::*;

verus! {

fn bitwise_xor(a: &[u32], b: &[u32]) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> b[i] <= 65535,
    ensures 
        res.len() == a.len(),
        forall|i: int| #![trigger res[i]] 0 <= i < a.len() ==> {
            res[i] == (#[verifier::truncate] (a[i] as u16) ^ #[verifier::truncate] (b[i] as u16)) as u32
        },
{
    let mut result: Vec<u32> = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            a.len() == b.len(),
            result.len() == idx,
            forall|i: int| #![trigger result[i as int]] 0 <= i < idx ==> {
                result[i as int] == (#[verifier::truncate] (a[i] as u16) ^ #[verifier::truncate] (b[i] as u16)) as u32
            },
        decreases a.len() - idx,
    {
        let a_val = #[verifier::truncate] (a[idx] as u16);
        let b_val = #[verifier::truncate] (b[idx] as u16);
        let xor_result = a_val ^ b_val;
        result.push(xor_result as u32);
        idx += 1;
    }
    
    result
}

}

fn main() {}