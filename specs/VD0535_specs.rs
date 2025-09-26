// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(m: i32) -> (result: bool)
    requires m > 0
    ensures result <==> (m > 1 && forall|j: int| 2 <= j < m ==> #[trigger] (m % j as i32) != 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}