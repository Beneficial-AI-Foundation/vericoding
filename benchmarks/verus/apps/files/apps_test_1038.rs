// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(a: int, b: int) -> bool {
    0 <= a <= b
}

spec fn xor_int(x: int, y: int) -> int
    requires x >= 0 && y >= 0,
    decreases x + y,
{
    if x == 0 && y == 0 { 0 }
    else if x == 0 { y }
    else if y == 0 { x }
    else {
        let bit_x = x % 2;
        let bit_y = y % 2;
        let xor_bit = if bit_x != bit_y { 1 } else { 0 };
        xor_bit + 2 * xor_int(x / 2, y / 2)
    }
}

spec fn xor_range(a: int, b: int) -> int
    requires 0 <= a <= b,
    decreases b - a,
{
    if a == b { a }
    else { xor_int(a, xor_range(a + 1, b)) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(a: int, b: int) -> (result: int)
    requires valid_input(a, b)
    ensures result == xor_range(a, b)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}