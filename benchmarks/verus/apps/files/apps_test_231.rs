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
// </vc-spec>
// <vc-code>
/* placeholder implementation */
// </vc-code>


}

fn main() {}