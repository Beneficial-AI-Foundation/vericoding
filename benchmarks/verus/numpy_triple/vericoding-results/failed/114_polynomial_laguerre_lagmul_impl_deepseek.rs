// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed f64 multiplier lemma and seq creation */
proof fn non_zero_product_implies_non_zero_factors(a: f64, b: f64)
    ensures
        a.mul(b) != 0.0 ==> a != 0.0 && b != 0.0
{
}

proof fn lemma_seq_creation() ensures Seq::<f64>::new(3, |i| 0.0).len() == 3 { }
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
    /* code modified by LLM (iteration 5): fixed sequence creation syntax */
    let n = c1.len();
    let m = c2.len();
    let result_len = n + m - 1;
    let mut result = Vec::with_capacity(result_len);
    
    result.resize(result_len, 0.0);
    
    for i in 0..n {
        for j in 0..m {
            let product = c1[i] * c2[j];
            let idx = i + j;
            result[idx] = result[idx] + product;
        }
    }
    
    result
}
// </vc-code>

}
fn main() {}