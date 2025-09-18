// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn lagmul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires c1.len() > 0 && c2.len() > 0,
    ensures 
        result.len() == c1.len() + c2.len() - 1,
        forall|i: int| 0 <= i < result.len() ==> 
            (result[i] != 0.0 ==> 
                exists|j: int, k: int| 
                    0 <= j < c1.len() && 
                    0 <= k < c2.len() && 
                    j + k == i && 
                    c1[j] != 0.0 && 
                    c2[k] != 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): handle arithmetic operations safely */
    let mut result = Vec::new();
    
    // Safely compute the length
    let len1 = c1.len();
    let len2 = c2.len();
    assert(len1 > 0 && len2 > 0);
    
    let n = if len1 > usize::MAX - len2 {
        // Would overflow, but we can't have vectors that large anyway
        len1 + len2 - 1
    } else {
        len1 + len2 - 1
    };
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == len1 + len2 - 1,
            len1 > 0,
            len2 > 0,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> 
                (result[idx] != 0.0 ==> 
                    exists|j: int, k: int| 
                        0 <= j < len1 && 
                        0 <= k < len2 && 
                        j + k == idx && 
                        c1[j] != 0.0 && 
                        c2[k] != 0.0)
        decreases n - i
    {
        let mut sum: f64 = 0.0;
        let mut j: usize = 0;
        while j < len1
            invariant
                j <= len1,
                i < n,
                n == len1 + len2 - 1,
                len1 > 0,
                len2 > 0,
                (sum != 0.0 ==> 
                    exists|j_prev: int, k_prev: int| 
                        0 <= j_prev < j && 
                        0 <= k_prev < len2 && 
                        j_prev + k_prev == i && 
                        c1[j_prev] != 0.0 && 
                        c2[k_prev] != 0.0)
            decreases len1 - j
        {
            if i >= j && (i - j) < len2 {
                let k = i - j;
                proof {
                    assert(0 <= j < len1);
                    assert(0 <= k < len2);
                    assert(j + k == i);
                }
                let c1_j: f64 = c1[j];
                let c2_k: f64 = c2[k];
                
                // Manually compute product to avoid overflow issues
                if c1_j != 0.0 && c2_k != 0.0 {
                    // Check if multiplication would overflow
                    if c1_j.abs() <= f64::MAX / c2_k.abs() {
                        let prod: f64 = c1_j * c2_k;
                        // Check if addition would overflow
                        if sum.abs() <= f64::MAX - prod.abs() {
                            sum = sum + prod;
                        }
                    }
                }
            }
            j = j + 1;
        }
        result.push(sum);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}