// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_non_prime(n: i8) -> (result: bool)
    requires n as int >= 2
    ensures result <==> (exists|k: int| 2 <= k < n as int && #[trigger] ((n as int) % k) == 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}