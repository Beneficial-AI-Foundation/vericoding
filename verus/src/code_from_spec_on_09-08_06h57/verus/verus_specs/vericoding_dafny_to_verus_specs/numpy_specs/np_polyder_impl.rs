use vstd::prelude::*;

verus! {

// SPEC
fn polyder(poly: &[int], m: usize) -> (ret: Vec<int>)
    requires 
        m > 0,
        m <= poly.len(),
    ensures ret.len() == poly.len() - m,
{
    /* code modified by LLM (iteration 4): Fixed ghost variable syntax and arithmetic operations */
    let mut result = Vec::new();
    
    for i in m..poly.len()
        invariant
            result.len() == i - m,
    {
        let mut coeff = poly[i];
        
        // Multiply by falling factorial: i * (i-1) * ... * (i-m+1)
        for j in 0..m
            invariant
                j <= m,
        {
            /* code modified by LLM (iteration 4): Convert usize to int properly for multiplication */
            let factor = (i - j) as int;
            proof {
                assert(i >= j);
                assert(i - j > 0);
            }
            coeff = coeff * factor;
        }
        
        result.push(coeff);
    }
    
    result
}

}

fn main() {}