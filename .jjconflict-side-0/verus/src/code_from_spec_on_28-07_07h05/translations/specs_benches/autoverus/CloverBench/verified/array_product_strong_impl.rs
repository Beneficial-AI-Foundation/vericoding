use vstd::prelude::*;

fn main() {}
verus! {

fn product(a: &Vec<u32>, b: &Vec<u32>) -> (c: Vec<u32>)
    requires
        a.len() <= 100 && a.len() == b.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> (a[i] * b[i] < 1000),
    ensures
        c@.len() == a@.len(),
        forall|i: int| (0 <= i && i < a.len()) ==> c[i] == #[trigger] a[i] * #[trigger] b[i],
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    /* code modified by LLM (iteration 4): fixed bounds checking and type consistency */
    while i < a.len()
        invariant
            i <= a.len(),
            result@.len() == i,
            forall|j: int| (0 <= j && j < i) ==> result[j] == a[j] * b[j],
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 4): added bounds assertion with correct syntax for sequence length */
        assert(i < a.len());
        assert(i < b.len());
        assert(0 <= i as int && i as int < a@.len());
        assert(0 <= i as int && i as int < b@.len());
        
        /* code modified by LLM (iteration 4): ensured arithmetic bounds before multiplication */
        assert(a[i as int] * b[i as int] < 1000);
        
        result.push(a[i] * b[i]);
        i += 1;
    }
    
    result
}

} // verus!