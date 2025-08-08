use vstd::prelude::*;

verus! {

fn equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (a[i] == b[i])
{
    let mut res = Vec::with_capacity(a.len());
    let mut i = 0;
    
    while i < a.len()
        invariant 
            0 <= i <= a.len(),
            res.len() == i,
            a.len() == b.len(),
            forall|j: int| 0 <= j < i ==> res[j] == (a[j as int] == b[j as int])
        decreases a.len() - i
    {
        assert(i < a.len());
        assert(a.len() == b.len());
        assert(i < b.len());
        res.push(a[i] == b[i]);
        i += 1;
    }
    
    res
}

}

fn main() {}