use vstd::prelude::*;

verus! {

fn less_equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == (a@[i] <= b@[i])
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == (a@[i] <= b@[i])
    {
        let comparison = a[idx] <= b[idx];
        result.push(comparison);
        idx += 1;
    }
    
    result
}

}

fn main() {}