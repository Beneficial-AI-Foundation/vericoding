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
    let mut i = 0;
    
    /* code modified by LLM (iteration 4): fixed loop invariant bounds and added proper assertions */
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result@.len() == i,
            forall|j: int| #![auto] (0 <= j && j < i && j < result@.len()) ==> result[j] == a[j] * b[j],
            a.len() == b.len(),
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 4): properly use precondition to prove assertion */
        assert(i < a.len());
        assert(i < b.len()) by {
            assert(a.len() == b.len());
        }
        assert(a[i as int] * b[i as int] < 1000) by {
            assert(0 <= i && i < a.len());
            assert(forall|k: int| (0 <= k && k < a.len()) ==> (a[k] * b[k] < 1000));
        }
        
        result.push(a[i] * b[i]);
        i += 1;
    }
    
    result
}

} // verus!