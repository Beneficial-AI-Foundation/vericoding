use vstd::prelude::*;

verus! {

fn bitwise_and(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> b[i] <= 65535,
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == ((#[verifier::truncate] (a[i] as u16)) & (#[verifier::truncate] (b[i] as u16))) as u32,
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == ((#[verifier::truncate] (a[j] as u16)) & (#[verifier::truncate] (b[j] as u16))) as u32,
        decreases a.len() - i,
    {
        proof {
            assert(i < a.len());
            assert(i < b.len());
        }
        let val = ((#[verifier::truncate] (a[i] as u16)) & (#[verifier::truncate] (b[i] as u16))) as u32;
        res.push(val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}