use vstd::prelude::*;

verus! {

fn bitwise_or(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] <= 65535 && b[i] <= 65535,
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (#[verifier::truncate] (a[i] as u16) | #[verifier::truncate] (b[i] as u16)) as u32,
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == (#[verifier::truncate] (a[j] as u16) | #[verifier::truncate] (b[j] as u16)) as u32,
        decreases a.len() - i,
    {
        let val = (#[verifier::truncate] (a[i] as u16) | #[verifier::truncate] (b[i] as u16)) as u32;
        res.push(val);
        i += 1;
    }
    
    res
}

fn bitwise_or_bv32(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == (a[i] | b[i]),
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == (a[j] | b[j]),
        decreases a.len() - i,
    {
        let val = a[i] | b[i];
        res.push(val);
        i += 1;
    }
    
    res
}

}

fn main() {}