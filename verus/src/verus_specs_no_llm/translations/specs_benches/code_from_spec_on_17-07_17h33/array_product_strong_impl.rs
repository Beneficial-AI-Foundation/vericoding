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
    
    /* code modified by LLM (iteration 1): added proper bounds checking, cast i to int, and overflow prevention */
    while i < a.len()
        invariant
            result@.len() == i,
            0 <= i <= a.len(),
            a.len() == b.len(),
            forall|j: int| (0 <= j && j < i) ==> result[j] == a[j] * b[j],
        decreases a.len() - i,
    {
        /* code modified by LLM (iteration 1): assert bounds before array access */
        assert(i < a.len());
        assert(i < b.len());
        /* code modified by LLM (iteration 3): fixed type casting for length comparison */
        assert(0 <= i as int && i as int < a.len() as int);
        assert(0 <= i as int && i as int < b.len() as int);
        
        /* code modified by LLM (iteration 1): assert multiplication bounds to prevent overflow */
        assert(a[i as int] * b[i as int] < 1000);
        
        result.push(a[i] * b[i]);
        i += 1;
    }
    
    /* code modified by LLM (iteration 1): assert final length equality */
    assert(result@.len() == a@.len());
    
    return result;
}

} // verus!