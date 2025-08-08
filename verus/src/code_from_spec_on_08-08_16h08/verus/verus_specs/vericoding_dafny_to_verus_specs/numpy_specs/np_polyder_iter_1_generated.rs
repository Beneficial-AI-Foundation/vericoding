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
        let mut coeff = poly[i + m];
        
        // Multiply by the factorial-like term: (i+m)! / i!
        for j in 0..m
            invariant coeff == poly[i + m] * factorial_range(i + 1, i + m)
        {
            coeff = coeff * (i + j + 1) as int;
        }
        
        result.push(coeff);
    }
    
    result
}

// Helper function to compute the product (start) * (start+1) * ... * (end)
spec fn factorial_range(start: usize, end: usize) -> int {
    if start > end {
        1
    } else {
        (start as int) * factorial_range(start + 1, end)
    }
}

}

fn main() {}