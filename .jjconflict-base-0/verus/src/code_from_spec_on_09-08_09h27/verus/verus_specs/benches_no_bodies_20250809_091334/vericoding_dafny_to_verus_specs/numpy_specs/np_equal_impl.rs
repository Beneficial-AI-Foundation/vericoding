use vstd::prelude::*;

verus! {

fn equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res[i] == (a[i] == b[i]),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < a.len()
        invariant 
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result[i] == (a[i] == b[i]),
        decreases a.len() - idx,
    {
        let are_equal = a[idx] == b[idx];
        result.push(are_equal);
        idx += 1;
    }
    
    result
}

} // verus!

fn main() {}