// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n >= 1
}

spec fn sum_from_one_to_n(n: int) -> int
    recommends n >= 1
{
    n * (n + 1) / 2
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn sum_to_n(n: int) -> (result: int)
    requires valid_input(n)
    ensures result == sum_from_one_to_n(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}