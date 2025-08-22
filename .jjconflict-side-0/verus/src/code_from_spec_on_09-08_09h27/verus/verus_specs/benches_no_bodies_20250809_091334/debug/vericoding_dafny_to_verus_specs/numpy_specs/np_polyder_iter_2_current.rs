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
    let mut i = m;
    
    while i < poly.len()
        invariant
            i >= m,
            i <= poly.len(),
            result.len() == i - m,
    {
        /* code modified by LLM (iteration 1): cast usize to int for array indexing */
        let mut coeff = poly[i as int];
        let mut j = 0;
        
        while j < m
            invariant
                j <= m,
                coeff == poly[i as int] * factorial(i, j),
        {
            /* code modified by LLM (iteration 1): cast usize subtraction to int for multiplication */
            coeff = coeff * ((i - j) as int);
            j = j + 1;
        }
        
        result.push(coeff);
        i = i + 1;
    }
    
    result
}

spec fn factorial(n: usize, k: usize) -> int
    requires k <= n
    decreases k
{
    if k == 0 {
        1
    } else {
        /* code modified by LLM (iteration 1): ensure k > 0 before subtracting to avoid underflow */
        (n - k + 1) as int * factorial(n, k - 1)
    }
}

}

fn main() {}