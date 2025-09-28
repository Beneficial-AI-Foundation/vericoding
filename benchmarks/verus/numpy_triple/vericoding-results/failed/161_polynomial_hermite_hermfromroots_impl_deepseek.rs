// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed spec_neg usage and simplified polynomial lemma */
proof fn polynomial_mul_lemma(a: Seq<f32>, b: Seq<f32>, c: Seq<f32>) 
    requires
        a.len() >= 1,
        b.len() >= 1,
        c.len() == a.len() + b.len() - 1,
        forall|i: int| 0 <= i < a.len() ==> a[i] == c[i],
        forall|j: int| 0 <= j < b.len() ==> b[j] == c[j + a.len() - 1]
    ensures
        forall|k: int| 0 <= k < c.len() ==> c[k] == (if k < a.len() { a[k] } else { b[k - a.len() + 1] })
{
}

spec fn neg_f32(x: f32) -> f32 {
    -x
}
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed f32 operations and simplified implementation */
    let n = roots.len();
    if n == 0 {
        return vec![1.0f32];
    }
    
    let mut coef = Vec::<f32>::new();
    coef.push(1.0f32);
    coef.push(-roots[0]);
    
    let mut i = 1;
    while i < n
        invariant
            i <= n,
            coef@.len() == i + 1
    {
        let root = roots[i];
        let last_coef = coef.clone();
        coef.push(0.0f32);
        
        let mut j = i;
        while j > 0
            invariant
                j <= i,
                coef@.len() == i + 2
        {
            coef[j] = coef[j] - root * coef[j - 1];
            j = j - 1;
        }
        coef[0] = -root * coef[0];
        
        i = i + 1;
    }
    
    coef
}
// </vc-code>


}
fn main() {}