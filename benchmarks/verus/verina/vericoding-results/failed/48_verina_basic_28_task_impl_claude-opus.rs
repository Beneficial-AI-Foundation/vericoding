// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): convert nat to u32 for execution, maintain spec correctness */
    let n_u32 = n as u32;
    let mut i: u32 = 2;
    while i < n_u32
        invariant
            2 <= i <= n_u32,
            n_u32 == n,
            forall|k: nat| 2 <= k < i as nat ==> (n % k) != 0,
    {
        if n_u32 % i == 0 {
            proof {
                assert(n % (i as nat) == 0);
                assert(2 <= i as nat < n);
            }
            return false;
        }
        i = i + 1;
    }
    proof {
        assert(i == n_u32);
        assert(forall|k: nat| 2 <= k < n ==> (n % k) != 0);
    }
    true
}
// </vc-code>

}
fn main() {}