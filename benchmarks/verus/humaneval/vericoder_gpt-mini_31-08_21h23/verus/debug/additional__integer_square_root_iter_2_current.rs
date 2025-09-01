use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helpers needed
// </vc-helpers>

// <vc-spec>
fn integer_square_root(n: i32) -> (result: i32)
    // pre-conditions-start
    requires
        n >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        0 <= result * result,
        result * result <= n,
        n < (result + 1) * (result + 1)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut r: int = 0;
    while (r + 1) * (r + 1) <= (n as int)
        invariant 0 <= r && r * r <= (n as int)
        decreases (n as int) - r * r
    {
        r = r + 1;
    }
    // r is non-negative and r*r <= n, and n fits in i32, so r fits in i32
    r as i32
}
// </vc-code>

fn main() {}
}