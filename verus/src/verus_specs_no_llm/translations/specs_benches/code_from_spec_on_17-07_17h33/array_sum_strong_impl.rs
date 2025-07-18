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
    /* code modified by LLM (iteration 2): changed i to usize to match Rust indexing */
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 2): updated invariants to use proper type conversions */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a.len() == b.len(),
            result@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> result[j] == a[j] + b[j],
            forall|j: int| (0 <= j && j < a.len()) ==> (a[j] + b[j] < 1000),
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 2): added proper type conversion for assertions */
        assert(i < a.len());
        assert(i < b.len());
        assert(a[i as int] + b[i as int] < 1000);
        
        result.push(a[i] + b[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 2): updated final assertions with proper types */
    assert(result@.len() == i);
    assert(i == a.len());
    
    result
}

} // verus!