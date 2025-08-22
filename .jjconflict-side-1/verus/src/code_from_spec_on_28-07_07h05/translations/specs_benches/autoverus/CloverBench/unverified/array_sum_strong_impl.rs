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
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): fixed bounds checking and type conversions */
    while i < a.len()
        invariant
            i <= a.len(),
            a.len() == b.len(),
            result@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> result[j] == a[j] + b[j],
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 4): use a@.len() for abstract length in specifications */
        assert(0 <= i as int && i as int < a@.len());
        assert(a[i as int] + b[i as int] < 1000);
        result.push(a[i] + b[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 4): added final assertion to help prove postcondition */
    assert(result@.len() == a@.len());
    result
}

} // verus!