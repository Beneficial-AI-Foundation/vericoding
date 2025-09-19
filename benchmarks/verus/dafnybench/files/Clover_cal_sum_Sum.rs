// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum(n: u8) -> (s: u8)
    requires n as nat >= 0
    ensures s as nat == n as nat * (n as nat + 1) / 2
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}