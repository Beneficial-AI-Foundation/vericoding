use vstd::prelude::*;

verus! {

// SPEC
fn polyder(poly: &[int], m: usize) -> (ret: Vec<int>)
    requires 
        m > 0,
        m <= poly.len(),
    ensures ret.len() == poly.len() - m,
{
    let mut result = Vec::new();
    let target_len = poly.len() - m;
    
    for i in 0..target_len
        invariant result.len() == i
    {
        /* code modified by LLM (iteration 3): fixed type casting and removed int usage in executable code */
        let base_coeff = poly[i + m];
        let mut coeff = base_coeff;
        
        // Multiply by the factorial-like term: (i+m)! / i!
        for j in 0..m
            invariant 
                coeff == poly[i + m] * factorial_range((i + 1) as int, (i + j + 1) as int),
        {
            /* code modified by LLM (iteration 3): use usize arithmetic for executable code */
            coeff = coeff * (i + j + 1);
        }
        
        result.push(coeff);
    }
    
    result
}

// Helper function to compute the product (start) * (start+1) * ... * (end)
spec fn factorial_range(start: int, end: int) -> int {
    if start > end {
        1
    } else {
        start * factorial_range(start + 1, end)
    }
}

}

fn main() {}