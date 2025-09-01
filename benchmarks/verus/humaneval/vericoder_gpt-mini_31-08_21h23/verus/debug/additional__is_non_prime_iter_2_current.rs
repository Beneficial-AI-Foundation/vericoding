use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed for this proof.
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
    let mut k: u32 = 2;
    let mut found: bool = false;
    let mut found_k: u32 = 0;
    while k < n
        invariant 2 <= k as int;
        invariant k <= n;
        invariant forall|j: int| 2 <= j && j < (k as int) ==> (n as int % j) != 0;
        decreases (n - k)
    {
        if n % k == 0 {
            found = true;
            found_k = k;
            break;
        }
        k = k + 1;
    }

    if found {
        proof {
            // found_k was set when k < n and n % k == 0
            assert(2 <= found_k as int);
            assert(found_k as int < n as int);
            assert((n as int) % (found_k as int) == 0);
            // introduce the existential for the postcondition with an explicit witness
            assert(exists|i: int| i == (found_k as int) && 2 <= i && i < n as int && #[trigger] (n as int % i) == 0);
        }
        true
    } else {
        proof {
            // loop exited without finding a divisor, so k == n
            assert(k == n);
            // invariant gives no divisor for all j in [2, n-1]
            assert(forall|i: int| 2 <= i && i < n as int ==> (n as int % i) != 0);
            // hence there does not exist a divisor in that range
            assert(!(exists|i: int| 2 <= i && i < n as int && #[trigger] (n as int % i) == 0));
        }
        false
    }
    // impl-end
}
// </vc-code>

fn main() {}
}