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
        /* code modified by LLM (iteration 2): compute coefficient using ghost variables and proof block */
        let base_coeff = poly[i];
        let mut coeff: int;
        
        proof {
            let mut temp_coeff = base_coeff;
            let mut j = 0;
            
            while j < m
                invariant
                    j <= m,
                    temp_coeff == base_coeff * factorial(i, j),
            {
                temp_coeff = temp_coeff * ((i - j) as int);
                j = j + 1;
            }
            coeff = temp_coeff;
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