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
    let mut res = Vec::with_capacity(a.len());
    
    for i in 0..a.len()
        invariant 
            res.len() == i,
            a.len() == b.len(),
            forall|k: int| 0 <= k < b.len() ==> b[k] != 0,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] % b[j],
    {
        let mod_result = a[i] % b[i];
        res.push(mod_result);
    }
    
    res
}

}

fn main() {}