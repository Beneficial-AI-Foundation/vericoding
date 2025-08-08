use vstd::prelude::*;

verus! {

fn equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len(),
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == (a@[i] == b@[i]),
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause and fixed indexing syntax */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] == b@[j]),
        decreases a.len() - i,
    {
        let are_equal = a[i] == b[i];
        result.push(are_equal);
        i += 1;
    }
    
    result
}

} // verus!

fn main() {}