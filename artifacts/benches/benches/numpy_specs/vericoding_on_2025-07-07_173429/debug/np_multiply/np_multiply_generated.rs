use vstd::prelude::*;

verus! {

fn multiply(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res@[i] == a[i].wrapping_mul(b[i]),
{
    let mut res = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            res.len() == idx,
            a.len() == b.len(),
            forall|j: int| #![auto] 0 <= j < idx ==> res@[j] == a[j].wrapping_mul(b[j]),
        decreases a.len() - idx,
    {
        res.push(a[idx].wrapping_mul(b[idx]));
        idx = idx + 1;
    }
    
    res
}

}

fn main() {}