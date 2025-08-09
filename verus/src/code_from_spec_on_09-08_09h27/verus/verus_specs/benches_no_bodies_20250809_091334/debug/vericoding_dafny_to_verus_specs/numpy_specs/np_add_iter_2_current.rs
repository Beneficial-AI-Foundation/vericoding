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
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause for loop termination */
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            forall|i: int| 0 <= i < idx ==> res[i] == a[i] + b[i],
        decreases a.len() - idx,
    {
        res.push(a[idx] + b[idx]);
        idx += 1;
    }
    
    res
}

}

fn main() {}