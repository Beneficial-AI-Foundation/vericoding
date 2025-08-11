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
        /* code modified by LLM (iteration 3): compute coefficient using ghost variables and proof block with proper types */
        let base_coeff = poly[i];
        let mut coeff: int;
        
        proof {
            let mut temp_coeff = base_coeff;
            let mut j: usize = 0;
            
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
        /* code modified by LLM (iteration 3): fix type mismatch by ensuring k-1 is usize */
        (n - k + 1) as int * factorial(n, (k - 1) as usize)
    }
}

}

fn main() {}