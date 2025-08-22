use vstd::prelude::*;

fn main() {}
verus! {

fn copy(a: &Vec<u64>) -> (b: Vec<u64>)
    requires
        a.len() <= 100,
    ensures
        b@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> b[i] == a[i],
{
    let mut b = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            b@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> b[j] == a[j],
        decreases a.len() - i,
    {
        b.push(a[i]);
        i = i + 1;
    }
    
    b
}

} // verus!