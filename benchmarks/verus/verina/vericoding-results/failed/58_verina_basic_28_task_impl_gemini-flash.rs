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
/* code modified by LLM (iteration 5): removed unnecessary curly braces around invariant `forall` */
{
    let mut i: nat = 2;
    while i < n
        invariant 2 <= i <= n,
        invariant (forall|k: nat| 2 <= k < i ==> (n % k) != 0),
        decreases n - i
    {
        if n % i == 0 {
            return false;
        }
        i = i + 1;
    }
    return true;
}
// </vc-code>

}
fn main() {}