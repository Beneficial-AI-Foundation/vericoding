use vstd::prelude::*;

fn main() {}
verus! {

fn sum(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] + b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] + #[trigger] b[i],
{
    let mut c = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            c@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> c[j] == a[j] + b[j],
    {
        c.push(a[i] + b[i]);
        i = i + 1;
    }
    
    c
}

} // verus!