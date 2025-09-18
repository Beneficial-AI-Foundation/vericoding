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
    /* code modified by LLM (iteration 5): Fixed compilation error by enclosing loop invariants in curly braces */
    let mut i: nat = 2;
    while i < n
        invariant {
            2 <= i <= n,
            forall|j: nat| j >= 2 && j < i ==> n % j != 0,
        }
        decreases n - i
    {
        if n % i == 0 {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-code>

}
fn main() {}