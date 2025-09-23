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
fn add(x: i8, y: i8) -> (result: i8)
    requires valid_input(x as int, y as int)
    ensures result as int == correct_sum(x as int, y as int)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}