use vstd::prelude::*;

verus! {

fn left_shift(a: &[i32], b: &[u32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] < 16,
        forall|i: int| 0 <= i < a.len() ==> a[i] < (1u16 as i32),
    ensures 
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res[i] == ((a[i] as u16) << (b[i] as u16)) as i32,
{
    let mut res: Vec<i32> = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| #![auto] 0 <= j < i ==> res[j] == ((a[j] as u16) << (b[j] as u16)) as i32,
            forall|k: int| 0 <= k < b.len() ==> b[k] < 16,
            forall|k: int| 0 <= k < a.len() ==> a[k] < (1u16 as i32),
        decreases a.len() - i,
    {
        let a_val = a[i];
        let b_val = b[i];
        
        let shifted_val = ((a_val as u16) << (b_val as u16)) as i32;
        res.push(shifted_val);
        i = i + 1;
    }
    
    res
}

}

fn main() {}