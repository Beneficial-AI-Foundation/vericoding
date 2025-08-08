use vstd::prelude::*;

verus! {

fn add(a: &[i32], b: &[i32]) -> (res: Vec<i32>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == a[i] + b[i],
{
    let mut res = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to fix verification error */
    while i < a.len()
        invariant
            i <= a.len(),
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == a[j] + b[j],
        decreases a.len() - i,
    {
        res.push(a[i] + b[i]);
        i += 1;
    }
    
    res
}

}

fn main() {}