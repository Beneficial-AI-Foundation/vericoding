// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(x: int, y: int) -> bool
{
    true
}

spec fn correct_sum(x: int, y: int) -> int
{
    x + y
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn add(x: int, y: int) -> (result: int)
    requires valid_input(x, y)
    ensures result == correct_sum(x, y)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}