use vstd::prelude::*;

verus! {

fn less_equal(a: &[i32], b: &[i32]) -> (res: Vec<bool>)
    requires a.len() == b.len()
    ensures 
        res.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> res@[i] == (a@[i] <= b@[i])
{
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == (a@[j] <= b@[j])
        decreases a.len() - i
    {
        let comparison = a[i] <= b[i];
        result.push(comparison);
        i += 1;
    }
    
    result
}

}

fn main() {}