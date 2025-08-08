use vstd::prelude::*;

verus! {

fn max(a: &[i32]) -> (res: i32)
    requires 
        a.len() > 0,
    ensures 
        exists|i: int| 0 <= i < a.len() && res == a[i],
        forall|i: int| 0 <= i < a.len() ==> a[i] <= res,
{
    let mut max_val = a[0];
    let mut idx = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while idx < a.len()
        invariant
            0 <= idx <= a.len(),
            exists|i: int| 0 <= i < a.len() && max_val == a[i],
            forall|i: int| 0 <= i < idx ==> a[i] <= max_val,
        decreases a.len() - idx,
    {
        if a[idx] > max_val {
            max_val = a[idx];
        }
        idx += 1;
    }
    
    max_val
}

fn main() {}

}