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
    let mut result = Vec::new();
    let mut i = 0;
    
    /* code modified by LLM (iteration 1): added decreases clause to prove loop termination */
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> result[j] == a[j] + b[j],
        decreases a.len() - i
    {
        result.push(a[i] + b[i]);
        i += 1;
    }
    
    result
}

} // verus!