// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(n: u8) -> (result: bool)
    requires n as nat >= 2,
    ensures
        result ==> forall|k: nat| 2 <= k < n as nat ==> #[trigger] ((n as nat) % k) != 0,
        !result ==> exists|k: nat| 2 <= k < n as nat && #[trigger] ((n as nat) % k) == 0,
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}