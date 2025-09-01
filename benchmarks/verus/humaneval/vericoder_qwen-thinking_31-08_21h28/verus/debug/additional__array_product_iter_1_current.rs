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
    let n = a.len();
    let mut result = Vec::new();
    for i in 0..n {
        invariant
            result.len() == i &&
            forall |j: int| #![auto] 0 <= j && j < result.len() ==> result[j] == (a[j] as i64) * (b[j] as i64);
        let val = (a[i] as i64) * (b[i] as i64);
        result.push(val);
        assert(result[i] == val);
    }
    result
}
// </vc-code>

fn main() {}
}