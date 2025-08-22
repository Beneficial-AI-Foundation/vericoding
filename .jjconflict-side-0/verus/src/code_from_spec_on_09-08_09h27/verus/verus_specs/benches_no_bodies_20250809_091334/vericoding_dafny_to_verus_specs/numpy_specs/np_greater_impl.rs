use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn greater(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires 
        a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == (a@[i] > b@[i]),
{
    let mut result = Vec::new();
    let mut idx = 0;
    
    while idx < a.len()
        invariant
            idx <= a.len(),
            result.len() == idx,
            forall|i: int| 0 <= i < idx ==> result@[i] == (a@[i] > b@[i]),
    {
        result.push(a[idx] > b[idx]);
        idx += 1;
    }
    
    result
}

}

fn main() {}