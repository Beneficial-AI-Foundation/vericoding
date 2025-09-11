// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(n: int) -> (result: bool)
    requires n >= 2
    ensures result <==> (forall|k: int| 2 <= k < n ==> #[trigger] (n % k) != 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}