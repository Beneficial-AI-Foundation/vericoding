use vstd::prelude::*;

verus! {

fn equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len(),
    ensures (
        res.len() == a.len()
        && forall|i: int| 0 <= i < a.len() ==> res[i] == (a[i] == b[i])
    )
{
    let mut res = Vec::new();
    let mut idx: usize = 0;
    
    while idx < a.len()
        invariant 
            a.len() == b.len(),
            0 <= idx <= a.len(),
            res.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> res[j] == (a[j] == b[j]),
        decreases a.len() - idx
    {
        res.push(a[idx] == b[idx]);
        idx = idx + 1;
    }
    
    res
}

}

fn main() {}