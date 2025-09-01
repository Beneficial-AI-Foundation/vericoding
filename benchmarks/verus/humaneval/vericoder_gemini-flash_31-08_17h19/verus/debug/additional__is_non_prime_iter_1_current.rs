use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn exists_k_divides_n(n: u32, limit: u32) -> (result: bool)
    requires n >= 2,
    ensures result == exists|k: int| 2 <= k < limit as int && #[trigger](n as int % k) == 0,
{
    let mut k = 2;
    while (k as u32) < limit
        invariant
            2 <= k,
            k as u32 <= limit,
            n >= 2,
            forall|j: int| 2 <= j < k ==> (n as int % j) != 0,
    {
        if n % k == 0 {
            return true;
        }
        k = k + 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn is_non_prime(n: u32) -> (result: bool)
    // pre-conditions-start
    requires
        n >= 2,
    // pre-conditions-end
    // post-conditions-start
    ensures
        result == exists|k: int| 2 <= k < n && #[trigger] (n as int % k) == 0,
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    // impl-start
    let mut k = 2;
    let n_int = n as int;

    while (k as u32) < n
        invariant
            2 <= k,
            k as u32 <= n,
            n >= 2,
            forall|j: int| 2 <= j < k ==> (n_int % j) != 0,
    {
        if n % k == 0 {
            assert(exists|x: int| 2 <= x < n_int && n_int % x == 0) by {
                assert(2 <= k && k < n_int);
                assert(n_int % k == 0);
                assert exists|x: int| 2 <= x < n_int && n_int % x == 0 by {
                    let x = k;
                    assert(x == k);
                    assert(2 <= x);
                    assert(x < n_int);
                    assert(n_int % x == 0);
                }
            }
            return true;
        }
        k = k + 1;
    }
    assert(forall|j: int| 2 <= j < k ==> (n_int % j) != 0);
    assert(k as u32 == n); // loop terminates when k == n
    assert(forall|j: int| 2 <= j < n_int ==> (n_int % j) != 0); // substitute k with n_int
    assert(!(exists|k_prime: int| 2 <= k_prime < n_int && (n_int % k_prime) == 0)); // negation of post_condition
    false
    // impl-end
}
// </vc-code>

fn main() {}
}