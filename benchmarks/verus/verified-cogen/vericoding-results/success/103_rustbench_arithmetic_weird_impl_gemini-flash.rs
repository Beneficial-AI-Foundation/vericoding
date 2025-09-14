// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn arithmetic_weird() -> (result: i32)
    ensures
        result < 10
// </vc-spec>
// <vc-code>
{
    let mut x: i32 = 0;
    while x < 5
        invariant
            x <= 5,
        decreases 5 - x
    {
        x = x + 1;
    }
    let result = x + 4;
    result
}
// </vc-code>

}
fn main() {}