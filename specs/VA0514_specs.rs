// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int, c: int) -> bool {
    1 <= b <= a <= 20 && 1 <= c <= 20
}

spec fn remaining_water(a: int, b: int, c: int) -> int
    recommends valid_input(a, b, c)
{
    let available_space = a - b;
    let remaining = c - available_space;
    if remaining >= 0 { remaining } else { 0 }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(input: Vec<i8>) -> (result: Vec<i8>)
    requires input.len() > 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}