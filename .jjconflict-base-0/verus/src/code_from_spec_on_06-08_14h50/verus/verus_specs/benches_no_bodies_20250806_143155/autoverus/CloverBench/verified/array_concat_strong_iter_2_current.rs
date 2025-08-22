use vstd::prelude::*;

fn main() {}
verus! {

fn concat(a: &Vec<u64>, b: &Vec<u64>) -> (c: Vec<u64>)
    requires
        a.len() <= 100 && b.len() <= 100,
    ensures
        c@.len() == a@.len() + b@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == a[i],
        forall|i: int| (a.len() <= i && i < c.len()) ==> c[i] == b[i - a.len()],
{
    let mut c = Vec::new();
    
    let mut i = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while i < a.len()
        invariant
            i <= a.len(),
            c@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> c[j] == a[j],
        decreases a.len() - i,
    {
        c.push(a[i]);
        i += 1;
    }
    
    let mut j = 0;
    /* code modified by LLM (iteration 1): added decreases clause for termination */
    while j < b.len()
        invariant
            j <= b.len(),
            c@.len() == a@.len() + j,
            forall|k: int| (0 <= k && k < a.len()) ==> c[k] == a[k],
            forall|k: int| (a.len() <= k && k < c@.len()) ==> c[k] == b[k - a.len()],
        decreases b.len() - j,
    {
        c.push(b[j]);
        j += 1;
    }
    
    c
}

} // verus!