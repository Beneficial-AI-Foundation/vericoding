use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    // impl-start
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0usize;
    while i < a.len() {
        invariant(i <= a.len());
        invariant(result.len() == i);
        invariant(forall |j: int| #![auto] 0 <= j && j < i as int ==> result[j as usize] == (a[j as usize] as i64) * (b[j as usize] as i64)));
        result.push((a[i] as i64) * (b[i] as i64));
        i += 1;
    }
    assert(result.len() == a.len());
    proof {
        // From the loop invariant and i == a.len(), conclude the postcondition
        assert(forall |k: int| #![auto] 0 <= k && k < i as int ==> result[k as usize] == (a[k as usize] as i64) * (b[k as usize] as i64]));
        assert(i == a.len());
        assert(forall |k: int| #![auto] 0 <= k && k < a.len() as int ==> result[k as usize] == (a[k as usize] as i64) * (b[k as usize] as i64]));
    }
    result
    // impl-end
}
// </vc-code>

fn main() {}
}