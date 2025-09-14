// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    requires
        a.len() == b.len(),
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Adding loop decreases clause and fixing invariant issues*/
{
    let mut result: Vec<i64> = Vec::new();
    result.reserve(a.len());

    let mut i = 0;
    while i < a.len()
        invariant
            0 <= i && i <= a.len(),
            result.len() == i,
            forall|k: int| 0 <= k && k < i ==> result[k] == (a[k] as i64) * (b[k] as i64),
        decreases a.len() - i
    {
        {
            let prod = (a[i] as i64) * (b[i] as i64);
            result.push(prod);
            i = i + 1;
        }
    }
    result
}
// </vc-code>

}
fn main() {}