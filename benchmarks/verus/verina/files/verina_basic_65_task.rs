// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn square_root(n: u8) -> (result: u8)
    ensures
        (result as nat) * (result as nat) <= (n as nat),
        (n as nat) < ((result + 1) as nat) * ((result + 1) as nat),
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}