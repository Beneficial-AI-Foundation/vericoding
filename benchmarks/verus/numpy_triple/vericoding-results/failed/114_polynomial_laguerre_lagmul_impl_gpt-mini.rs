// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): prove that a product being nonzero implies both factors are nonzero */
proof fn prod_nonzero_implies_factors_nonzero(a: f64, b: f64) ensures a * b != 0.0 ==> a != 0.0 && b != 0.0 { proof { if a * b != 0.0 { if a == 0.0 { assert(a * b == 0.0); } if b == 0.0 { assert(a * b == 0.0); } assert(a != 0.0); assert(b != 0.0); } } }
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
    /* code modified by LLM (iteration 5): implement convolution using usize indices to avoid ghost types */
    let len1: usize = c1.len();
    let len2: usize = c2.len();
    let n: usize = len1 + len2 - 1;

    let mut result: Vec<f64> = Vec::new();

    let mut t: usize = 0;
    while t < n {
        result.push(0.0);
        t += 1;
    }

    let mut i: usize = 0;
    while i < n {
        let mut j: usize = 0;
        while j < len1 {
            if i >= j {
                let k: usize = i - j;
                if k < len2 {
                    let term: f64 = c1[j] * c2[k];
                    let prev: f64 = result[i];
                    result[i] = prev + term;
                }
            }
            j += 1;
        }
        i += 1;
    }

    result
}
// </vc-code>

}
fn main() {}