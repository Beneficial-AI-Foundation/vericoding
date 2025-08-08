use vstd::prelude::*;

verus! {

fn less(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures
        res.len() == a.len(),
        forall|i: int| #![auto] 0 <= i < a.len() ==> res@[i] == (a@[i] < b@[i]),
{
    let mut res = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            res.len() == idx,
            forall|i: int| #![auto] 0 <= i < idx ==> res@[i] == (a@[i] < b@[i]),
    {
        res.push(a[idx] < b[idx]);
        idx += 1;
    }
    
    res
}

}

fn main() {}