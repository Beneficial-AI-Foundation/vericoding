use vstd::prelude::*;

verus! {

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn array_product(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i64>) by (nonlinear_arith)
    // pre-conditions-start
    requires
        a.len() == b.len(),
    // pre-conditions-end
    // post-conditions-start
    ensures
        result.len() == a.len(),
        forall|i: int| #![auto] 0 <= i && i < a.len() ==> result[i] == (a[i] as i64) * (b[i] as i64),
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<i64> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            i <= a.len(),
            result.len() == i,
            forall|j: int| #![auto] 0 <= j && j < i ==> result[j] == (a[j] as i64) * (b[j] as i64),
        decreases a.len() - i,
    {
        let product = (a[i] as i64) * (b[i] as i64);
        result.push(product);
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}