use vstd::prelude::*;

verus! {

fn mod_arrays(a: Vec<i32>, b: Vec<i32>) -> (res: Vec<i32>)
    requires
        a.len() == b.len(),
        forall|i: int| 0 <= i < b.len() ==> b[i] != 0,
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] % b[i],
{
    let mut res = Vec::new();
    let mut i: usize = 0;
    
    while i < a.len()
        invariant
            a.len() == b.len(),
            0 <= i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i@ ==> res[j] == a[j] % b[j],
        decreases a.len() - i,
    {
        res.push(a[i] % b[i]);
        i = i + 1;
    }
    
    res
}

}

fn main() {}