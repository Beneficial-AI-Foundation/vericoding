use vstd::prelude::*;

verus! {

// <vc-helpers>
#[verifier::loop_isolation(false)]
fn exists_k_divides_n(n: u32, limit: u32) -> (result: bool)
    requires n >= 2,
    ensures result == exists|k: int| 2 <= k < limit as int && (n as int % k) == 0,
{
    let mut k:u32 = 2; // k can be u32 directly
    while k < limit
        invariant
            2 <= k as int,
            k <= limit, 
            n >= 2,
            forall|j: int| 2 <= j < k as int ==> (n as int % j) != 0,
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
    let mut k: u32 = 2; // k can be u32 directly
    let n_int = n as int;

    while k < n
        invariant
            2 <= k as int,
            k <= n, // k is always less than or equal to n within the loop
            n >= 2,
            forall|j: int| 2 <= j < k as int ==> (n_int % j) != 0,
    {
        if n % k == 0 {
            assert(exists|x: int| 2 <= x < n_int && n_int % x == 0) by {
                let x_witness = k as int;
                assert(2 <= x_witness);
                assert(x_witness < n_int) by(nonlinear_arith) {
                    assert(k<n);
                }; // Since k < n is loop condition and n_int = n as int
                assert(n_int % x_witness == 0); // From n % k == 0
            }
            return true;
        }
        k = k + 1;
    }
    // After the loop, k will be equal to n because the loop continues as long as k < n.
    // If n is prime, none of the numbers from 2 to n-1 will divide n.
    // So, the loop will run until k reaches n.
    assert(k == n);
    proof {
        assert(forall|j: int| 2 <= j < k as int ==> (n_int % j) != 0); // From loop invariant
        assert(forall|j: int| 2 <= j < n_int ==> (n_int % j) != 0) by {
            assert(k as int == n_int);
        }; // substitute k with n_int
        assert(!exists|k_prime: int| 2 <= k_prime < n_int && (n_int % k_prime) == 0); // negation of post_condition
    }
    false
    // impl-end
}
// </vc-code>

fn main() {}
}