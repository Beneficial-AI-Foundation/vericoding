use vstd::prelude::*;

verus! {

fn right_shift(a: &Vec<u32>, b: &Vec<u32>) -> (res: Vec<u32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < a.len() ==> a[i] <= 65535,
        forall|i: int| 0 <= i < b.len() ==> b[i] < 16,
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == ((a[i] as u16) >> (b[i] as u32)) as u32,
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < a.len() ==> a[j] <= 65535,
            forall|j: int| 0 <= j < b.len() ==> b[j] < 16,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == ((a[j] as u16) >> (b[j] as u32)) as u32,
        decreases a.len() - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        let shifted = (#[verifier::truncate] (a_val as u16)) >> (b_val as u32);
        res.push(shifted as u32);
        i = i + 1;
    }
    
    res
}

fn main() {}

}