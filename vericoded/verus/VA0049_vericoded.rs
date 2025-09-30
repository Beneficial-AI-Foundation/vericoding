// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_rectangle_parts(a: int, b: int, n: int) -> bool {
    a > 0 && b > 0 && a != b && 2 * a + 2 * b == n
}

spec fn count_valid_rectangles(n: int) -> int
    recommends n > 0
{
    if n % 2 == 1 { 0 }
    else if n % 4 == 2 { n / 4 }
    else { n / 4 - 1 }
}

spec fn valid_input(n: int) -> bool {
    n > 0
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_i8_div_mod_small(n: i8)
    requires
        0 <= n as int,
    ensures
        (n % 2i8) as int == (n as int) % 2,
        (n / 2i8) as int == (n as int) / 2,
        (n % 4i8) as int == (n as int) % 4,
        (n / 4i8) as int == (n as int) / 4,
{
}

// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: i8)
    requires valid_input(n as int)
    ensures 
        result as int == count_valid_rectangles(n as int) &&
        (n as int % 2 == 1 ==> result as int == 0) &&
        (n as int % 2 == 0 && n as int % 4 == 2 ==> result as int == n as int / 4) &&
        (n as int % 2 == 0 && n as int % 4 == 0 ==> result as int == n as int / 4 - 1)
// </vc-spec>
// <vc-code>
{
    proof { lemma_i8_div_mod_small(n); }
    if n % 2i8 != 0i8 {
        0i8
    } else {
        let q: i8 = n / 4i8;
        if n % 4i8 == 2i8 {
            q
        } else {
            q - 1i8
        }
    }
}
// </vc-code>


}

fn main() {}