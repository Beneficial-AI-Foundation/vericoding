use vstd::prelude::*;

verus! {

// <vc-helpers>
// no helpers needed
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
    let mut i: usize = 0;
    while i < n
        invariant
            a.len() == n,
            b.len() == n,
            i <= n,
            result.len() == i,
            forall|j: int| #![auto] 0 <= j && j < i as int ==> result@[j] == (a@[j] as i64) * (b@[j] as i64),
    {
        let ai = a[i];
        let bi = b[i];
        result.push((ai as i64) * (bi as i64));
        i += 1;
    }
    result
}
// </vc-code>

fn main() {}
}