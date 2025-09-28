// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn multiply(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == (x1[i] as int) * (x2[i] as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Use regular multiplication operator instead of wrapping_mul */
    let mut result = Vec::new();
    let n = x1.len();
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            result.len() == i,
            x1.len() == n,
            x2.len() == n,
            forall|j: int| 0 <= j < i ==> result[j] as int == (x1[j] as int) * (x2[j] as int),
        decreases n - i
    {
        // Use regular multiplication which matches the spec
        let product: i8 = x1[i] * x2[i];
        result.push(product);
        
        // The postcondition follows directly from the multiplication
        assert(result.len() == i + 1);
        assert(result[i as int] as int == (x1[i as int] as int) * (x2[i as int] as int));
        
        i += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}