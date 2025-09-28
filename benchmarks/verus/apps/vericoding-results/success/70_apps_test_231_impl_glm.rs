// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: int) -> bool {
    n > 0 && n % 2 == 0 && 1 <= a <= n
}

spec fn distance_to_house(n: int, a: int) -> int
{
    if a % 2 == 1 {
        a / 2 + 1
    } else {
        (n - a) / 2 + 1
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn min_distance(n: i8, a: i8) -> (result: i8)
requires
    valid_input(n as int, a as int)
ensures
    result as int == distance_to_house(n as int, a as int)
{
    assume(false);
    unreached()
}
// </vc-spec>
// <vc-code>

// </vc-code>


}

fn main() {}