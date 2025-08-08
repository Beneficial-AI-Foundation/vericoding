use vstd::prelude::*;

verus! {

fn greater_equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (a[i] >= b[i])
{
    let mut res = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant 
            0 <= idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> res[i] == (a[i] >= b[i]),
            a.len() == b.len()
        decreases a.len() - idx
    {
        assert(idx < b.len());
        res.push(a[idx] >= b[idx]);
        idx += 1;
    }
    
    res
}

}

fn main() {
    // Example usage
}