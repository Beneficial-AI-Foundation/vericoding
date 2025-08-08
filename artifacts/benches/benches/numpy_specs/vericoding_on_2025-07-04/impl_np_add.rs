use vstd::prelude::*;

verus! {

fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i].wrapping_add(b[i]),
{
    let mut res = Vec::with_capacity(a.len());
    let mut i: usize = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> res[j] == a[j].wrapping_add(b[j]),
        decreases a.len() - i,
    {
        assert(i < a.len());
        assert(i < b.len());
        let sum = a[i].wrapping_add(b[i]);
        res.push(sum);
        i = i + 1;
    }
    
    res
}

} // verus!

fn main() {}