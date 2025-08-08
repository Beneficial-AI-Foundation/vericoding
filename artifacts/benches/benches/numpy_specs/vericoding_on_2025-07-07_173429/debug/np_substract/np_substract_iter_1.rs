use vstd::prelude::*;

verus! {

fn subtract(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res.view()[i] == a.view()[i].wrapping_sub(b.view()[i]),
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> res.view()[j] == a.view()[j].wrapping_sub(b.view()[j]),
        decreases a.len() - i,
    {
        let diff = a[i].wrapping_sub(b[i]);
        res.push(diff);
        i = i + 1;
    }
    
    res
}

}

fn main() {}