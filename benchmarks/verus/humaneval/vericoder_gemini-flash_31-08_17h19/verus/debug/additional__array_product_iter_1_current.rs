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

    // Loop invariant:
    // 1. result.len() == i
    // 2. For all j < i, result[j] == (a[j] as i64) * (b[j] as i64)
    // 3. result.spec().len() == i
    // 4. For all j < i, result.spec()[j] == (a.spec()[j] as i64) * (b.spec()[j] as i64)
    // 5. i <= n
    // 6. n == a.len()
    // 7. a.len() == b.len()
    // 8. a.spec().len() == n
    // 9. b.spec().len() == n
    // 10. `result` has sufficient capacity
    // 11. (result@.len() == i)
    // 12. (forall|k: int| 0 <= k && k < i ==> result@[k] == (a@[k] as i64) * (b@[k] as i64))
    // 13. (i <= n)
    // 14. (n == a.len())
    // 15. (a.len() == b.len())


    // Initialize result with a sufficient capacity to avoid reallocations,
    // which simplifies reasoning about ghost state updates.
    result.reserve_exact(n);

    let mut i = 0;
    while i < n
        invariant
            i: int,
            result: Vec<i64>,
            n: int,
            a: Vec<i32>,
            b: Vec<i32>,
            0 <= i,
            i <= n,
            n == a.len(),
            a.len() == b.len(),
            result.len() == i,
            result.spec().len() == i,
            forall|j: int| 0 <= j && j < i ==> result[j] == (a[j] as i64) * (b[j] as i64),
            forall|j: int| 0 <= j && j < i ==> result.spec()[j] == (a.spec()[j] as i64) * (b.spec()[j] as i64),
            result.capacity() >= n,
    {
        let prod = (a[i] as i64) * (b[i] as i64);
        result.push(prod);
        i = i + 1;
    }

    assert(result.len() == n);
    assert(result.spec().len() == n);

    proof {
        assert forall|idx: int| 0 <= idx && idx < a.len()
            implies result.spec()[idx] == (a.spec()[idx] as i64) * (b.spec()[idx] as i64) by {
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