// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn witness_of_divisor(n: nat, k: nat)
    requires 2 <= k && k < n && n % k == 0,
    ensures exists|i: nat| 2 <= i < n && n % i == 0
{
    proof {
        exists(k);
    }
}
// </vc-helpers>

// <vc-spec>
fn is_prime(n: nat) -> (result: bool)
    requires n >= 2,
    ensures
        result ==> forall|k: nat| 2 <= k < n ==> #[trigger] (n % k) != 0,
        !result ==> exists|k: nat| 2 <= k < n && #[trigger] (n % k) == 0,
// </vc-spec>
// <vc-code>
{
    let mut k: nat = 2;
    let mut div: nat = 0;
    let mut found: bool = false;
    while k < n
        invariant
            k <= n,
            forall|i: nat| 2 <= i < k ==> n % i != 0,
        decreases n - k
    {
        if n % k == 0 {
            div = k;
            found = true;
            break;
        }
        k = k + 1;
    }
    if found {
        proof {
            witness_of_divisor(n, div);
        }
        return false;
    } else {
        proof {
            // from the invariant and k <= n, when loop exits we have k == n
            assert(!(k < n));
            assert(k <= n);
            assert(k == n);
            assert(forall|i: nat| 2 <= i < n ==> n % i != 0);
        }
        return true;
    }
}
// </vc-code>

}
fn main() {}