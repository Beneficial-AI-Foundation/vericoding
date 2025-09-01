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
    let mut result: Vec<i64> = Vec::new();
    for index in 0..n
        invariant
            result.len() == index,
            forall |j: int| #[trigger] result@[j] 0 <= j < index ==> result@[j] == (a@[j] as i64) * (b@[j] as i64)
    {
        result.push(((a[index] as i64) * (b[index] as i64)));
    }
    result
}
// </vc-code>

fn main() {}
}