// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix type mismatches by using proper nat operations */
fn divides(a: nat, b: nat) -> (result: bool)
    requires a > 0,
    ensures result == (b % a == 0),
{
    ((b as int) % (a as int)) == 0
}

proof fn no_divisors_in_range(n: nat, start: nat, end: nat)
    requires
        n >= 2,
        start <= end,
    ensures
        forall|k: nat| start <= k < end ==> !divides(k, n),
{
    reveal(divides);
    if start < end {
        assert(!divides(start, n));
        no_divisors_in_range(n, (start as int + 1) as nat, end);
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
/* code modified by LLM (iteration 5): Fix nat type conversion and arithmetic operations */
{
    if (n as int) == 2 {
        true
    } else {
        let mut i: nat = (2 as nat);
        while (i as int) < (n as int)
            invariant
                2 <= i <= n,
                forall|k: nat| 2 <= k < i ==> !divides(k, n),
        {
            proof {
                no_divisors_in_range(n, 2, i);
            }
            if divides(i, n) {
                return false;
            }
            i = ((i as int) + 1) as nat;
        }
        true
    }
}
// </vc-code>

}
fn main() {}