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
        let mut coeff = poly[i];
        let mut j = 0;
        
        while j < m
            invariant
                j <= m,
                coeff == poly[i] * factorial(i, j),
        {
            coeff = coeff * (i - j);
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
        (n - k + 1) * factorial(n, k - 1)
    }
}

}

fn main() {}