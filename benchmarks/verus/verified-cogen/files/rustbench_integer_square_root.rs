// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    requires
        n >= 1,
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}