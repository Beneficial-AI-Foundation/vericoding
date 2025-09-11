// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_perfect_square(n: nat) -> bool {
    exists|i: nat| #[trigger] (i * i) == n
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn is_perfect_square_fn(n: u64) -> (result: bool)
    ensures result <==> is_perfect_square(n as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}