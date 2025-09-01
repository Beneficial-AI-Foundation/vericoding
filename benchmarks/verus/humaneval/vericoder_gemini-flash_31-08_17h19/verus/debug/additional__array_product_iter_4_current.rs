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
    let mut result = Vec::new();
    let n = a.len();

    // Initialize result with a sufficient capacity to avoid reallocations,
    // which simplifies reasoning about ghost state updates.
    result.reserve_exact(n);

    let mut i = 0;
    while i < n
        invariant
            result.len() == i,
            result.view().len() == i, // Changed spec_len() to view().len()
            forall|j: int| 0 <= j && j < i ==> result.view()[j] == (a.view()[j] as i64) * (b.view()[j] as i64), // Changed view_nth() to view() and added array indexing
            i <= n,
            n == a.len(),
            a.len() == b.len(),
            result.capacity() >= n,
    {
        let prod = (a[i] as i64) * (b[i] as i64);
        result.push(prod);
        i = i + 1;
    }

    assert(result.len() == n);
    assert(result.view().len() == n); // Changed spec_len() to view().len()

    proof {
        assert forall|idx: int| 0 <= idx && idx < a.len()
            implies result.view()[idx] == (a.view()[idx] as i64) * (b.view()[idx] as i64) by { // Changed view_nth() to view() and added array indexing
            // This is directly covered by the loop invariant when i becomes n.
            // Specifically, `forall|j: int| 0 <= j && j < i ==> result.spec()[j] == (a.spec()[j] as i64) * (b.spec()[j] as i64)`
            // with `i == n` implies the postcondition.
        };
    }

    result
}
// </vc-code>

fn main() {}
}