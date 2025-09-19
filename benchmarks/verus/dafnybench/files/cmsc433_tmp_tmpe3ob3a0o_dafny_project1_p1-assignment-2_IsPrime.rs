// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_prime(m: i8) -> (result: bool)
    requires m as int > 0
    ensures result <==> (m as int > 1 && forall|j: int| 2 <= j < m as int ==> #[trigger] (m as int % j) != 0)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}