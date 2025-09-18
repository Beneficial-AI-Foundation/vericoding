// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn chebder(c: Vec<i32>, scl: i32) -> (result: Vec<i32>)
    requires c.len() > 0,
    ensures
        result.len() == c.len() - 1,
        c.len() > 1 ==> result[0] == scl * c[1],
        c.len() > 2 ==> result[1] == scl * 4 * c[2],
        forall|j: int| 2 <= j < result.len() ==>
            result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix initial state and loop bounds */
    let n = c.len();
    if n == 1 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    
    // Handle first element
    result.push(scl * c[1]);
    
    // Handle second element if it exists
    if n > 2 {
        result.push(scl * 4 * c[2]);
    }
    
    // Handle remaining elements
    if n > 3 {
        let mut j: usize = 2;
        while j < n - 1
            invariant
                2 <= j <= n - 1,
                result.len() == j,
                result.len() >= 1,
                n > 1 ==> result[0] == scl * c[1],
                n > 2 ==> result[1] == scl * 4 * c[2],
                forall|k: int| 2 <= k < j ==> result[k] == scl * (2 * ((k + 1) as i32)) * c[k + 1],
                j < n - 1 ==> j + 1 < n,
            decreases n - 1 - j
        {
            let coeff = scl * (2 * ((j + 1) as i32)) * c[j + 1];
            result.push(coeff);
            j = j + 1;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}